import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceCongruence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceCoefficientDepths
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceTorusCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedCongruencePointTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.Group

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped WithZero TensorProduct CategoryTheory.MonObj

set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceCongruence

open _root_.LinearAlgebraicGroups.Specs
open ExceptionalAffineBruhat ExceptionalAffineBuilding
open ExceptionalAffineRootSystems (ApartmentRoots threshold)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)

noncomputable section

/-- A trace-one element contracts the additive cocycle equation for a semilinear
action. This works also when the characteristic divides the extension degree. -/
theorem semilinearCocycleIsCoboundary
    {k K V : Type*} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    (ρ : Gal(K/k) → AddAut V)
    (hsmul : ∀ (σ : Gal(K/k)) (t : K) (v : V), ρ σ (t • v) = σ t • ρ σ v)
    (a : Gal(K/k) → V) (ha : ∀ σ τ, a (σ * τ) = a σ + ρ σ (a τ)) :
    ∃ b : V, ∀ σ, a σ = b - ρ σ b := by
  classical
  obtain ⟨t, ht⟩ := Algebra.trace_surjective k K (1 : k)
  have htrace : ∑ σ : Gal(K/k), σ t = 1 :=
    (trace_eq_sum_automorphisms (K := k) t).symm.trans (by rw [ht, map_one])
  let b : V := ∑ τ : Gal(K/k), τ t • a τ
  refine ⟨b, fun σ => eq_sub_of_add_eq ?_⟩
  have htranslate :
      (∑ τ : Gal(K/k), (σ * τ) t • a (σ * τ)) = b := by
    exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun τ => rfl)
  have hweights : ∑ τ : Gal(K/k), (σ * τ) t = 1 := by
    rw [← htrace]
    exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun τ => rfl)
  calc
    a σ + ρ σ b = (∑ τ : Gal(K/k), (σ * τ) t) • a σ + ρ σ b := by rw [hweights, one_smul]
    _ = ∑ τ : Gal(K/k), (σ * τ) t • a (σ * τ) := by
      change _ + ρ σ (∑ τ : Gal(K/k), τ t • a τ) = _
      rw [map_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro τ _
      rw [ha, smul_add, hsmul]
      rfl
    _ = b := htranslate

section Filtration

variable {Γ P : Type*} [Group Γ] [Group P]
variable (ρ : Γ →* MulAut P)

private theorem changedCocycleLaw (a : Γ → P)
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) (b : P) (σ τ : Γ) :
    b⁻¹ * a (σ * τ) * ρ (σ * τ) b =
      (b⁻¹ * a σ * ρ σ b) * ρ σ (b⁻¹ * a τ * ρ τ b) := by
  simp only [ha, map_mul, map_inv, MulAut.mul_apply]
  group

/-- Corrections along a separated congruence filtration give a coboundary
when the set of corrections is compact. This uses nested closed sets of
corrections, so no choice of a convergent subsequence of products is needed. -/
theorem compactFiltrationCoboundary [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] (hρ : ∀ σ, Continuous (ρ σ : P → P))
    (N : ℕ → Subgroup P) (hN : Antitone N)
    (hclosed : ∀ n, IsClosed (N n : Set P))
    (hsep : ∀ x : P, (∀ n, x ∈ N n) → x = 1)
    (hstep : ∀ n (c : Γ → P), (∀ σ τ, c (σ * τ) = c σ * ρ σ (c τ)) →
      (∀ σ, c σ ∈ N n) →
      ∃ d : N n, ∀ σ, (d : P)⁻¹ * c σ * ρ σ d ∈ N (n + 1))
    (a : Γ → P) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hfirst : ∀ σ, a σ ∈ N 0) :
    ∃ b : N 0, ∀ σ, a σ = (b : P) * (ρ σ b)⁻¹ := by
  let S (n : ℕ) : Set P := {b | b ∈ N 0 ∧ ∀ σ, b⁻¹ * a σ * ρ σ b ∈ N n}
  have hnest : Antitone S := fun _ _ h _ hb => ⟨hb.1, fun σ => hN h (hb.2 σ)⟩
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    have hset : S n = (N 0 : Set P) ∩
        ⋂ σ : Γ, (fun b : P => b⁻¹ * a σ * ρ σ b) ⁻¹' (N n : Set P) := by
      ext b
      simp [S]
    rw [hset]
    exact (hclosed 0).inter (isClosed_iInter fun σ => (hclosed n).preimage
      ((continuous_inv.mul continuous_const).mul (hρ σ)))
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, (N 0).one_mem, fun σ => ?_⟩
      simpa only [inv_one, one_mul, map_one, mul_one] using hfirst σ
    | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨d, hd⟩ := hstep n _ (changedCocycleLaw ρ a ha b) hb.2
      refine ⟨b * (d : P), (N 0).mul_mem hb.1 (hN (Nat.zero_le n) d.2), fun σ => ?_⟩
      simpa only [mul_inv_rev, map_mul, mul_assoc] using hd σ
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S (fun n => hnest (Nat.le_succ n)) hnonempty (hcl 0).isCompact hcl
  refine ⟨⟨b, (Set.mem_iInter.mp hb 0).1⟩, fun σ => ?_⟩
  have he := hsep (b⁻¹ * a σ * ρ σ b) (fun n => (Set.mem_iInter.mp hb n).2 σ)
  calc
    a σ = b * (b⁻¹ * a σ * ρ σ b) * (ρ σ b)⁻¹ := by group
    _ = b * (ρ σ b)⁻¹ := by rw [he, mul_one]

variable {k K V : Type*} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]

/-- A surjective leading-coordinate map with semilinear coefficient action
gives the correcting element for one congruence layer. -/
theorem semilinearLayerCorrection
    (ρ : Gal(K/k) →* MulAut P) (N N' : Subgroup P)
    (hstable : ∀ σ (n : N), ρ σ n ∈ N)
    (red : N →* Multiplicative V) (hsurj : Function.Surjective red)
    (hker : ∀ n : N, red n = 1 ↔ (n : P) ∈ N')
    (ψ : Gal(K/k) → AddAut V)
    (hsmul : ∀ (σ : Gal(K/k)) (t : K) (v : V), ψ σ (t • v) = σ t • ψ σ v)
    (hequiv : ∀ σ (n : N), (red ⟨ρ σ n, hstable σ n⟩).toAdd = ψ σ (red n).toAdd)
    (a : Gal(K/k) → P) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (hmem : ∀ σ, a σ ∈ N) :
    ∃ d : N, ∀ σ, (d : P)⁻¹ * a σ * ρ σ d ∈ N' := by
  let c (σ : Gal(K/k)) : N := ⟨a σ, hmem σ⟩
  have hc (σ τ : Gal(K/k)) : c (σ * τ) = c σ * ⟨ρ σ (c τ), hstable σ (c τ)⟩ :=
    Subtype.ext (ha σ τ)
  obtain ⟨b, hb⟩ := semilinearCocycleIsCoboundary ψ hsmul (fun σ => (red (c σ)).toAdd)
    (fun σ τ => by rw [hc, map_mul]; exact congrArg ((red (c σ)).toAdd + ·) (hequiv σ (c τ)))
  obtain ⟨d, hd⟩ := hsurj (Multiplicative.ofAdd b)
  refine ⟨d, fun σ => (hker (d⁻¹ * c σ * ⟨ρ σ d, hstable σ d⟩)).mp ?_⟩
  rw [map_mul, map_mul, map_inv, hd]
  change -b + (red (c σ)).toAdd + (red ⟨ρ σ d, hstable σ d⟩).toAdd = 0
  rw [hequiv, hd, hb]
  change -b + (b - ψ σ b) + ψ σ b = 0
  abel

/-- Use the actual coefficient-to-residue Galois isomorphism to perform a
compact succession of semilinear corrections in the original group. -/
theorem compactSemilinearCorrection
    [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (hρ : ∀ σ, Continuous (ρ σ : P → P))
    (e : Γ ≃* Gal(K/k)) (N : ℕ → Subgroup P) (hN : Antitone N)
    (hclosed : ∀ n, IsClosed (N n : Set P))
    (hsep : ∀ x : P, (∀ n, x ∈ N n) → x = 1)
    (layers : ∀ n, ∃ (index : Type*) (stable : ∀ σ (x : N n), ρ σ x ∈ N n)
      (red : N n →* Multiplicative (index → K)),
      Function.Surjective red ∧
      (∀ x : N n, red x = 1 ↔ (x : P) ∈ N (n + 1)) ∧
      ∀ σ (x : N n) i, (red ⟨ρ σ x, stable σ x⟩).toAdd i = e σ ((red x).toAdd i))
    (c : Γ → P) (hc : ∀ σ τ, c (σ * τ) = c σ * ρ σ (c τ))
    (hfirst : ∀ σ, c σ ∈ N 0) :
    ∃ b : N 0, ∀ σ, c σ = (b : P) * (ρ σ b)⁻¹ := by
  apply compactFiltrationCoboundary ρ hρ N hN hclosed hsep _ c hc hfirst
  intro n a ha hmem
  obtain ⟨index, stable, red, hs, hk, he⟩ := layers n
  let ρ' := ρ.comp e.symm.toMonoidHom
  let ψ (σ : Gal(K/k)) : AddAut (index → K) :=
    AddEquiv.piCongrRight (fun _ => σ.toRingEquiv.toAddEquiv)
  let a' (σ : Gal(K/k)) := a (e.symm σ)
  have ha' (σ τ : Gal(K/k)) : a' (σ * τ) = a' σ * ρ' σ (a' τ) := by
    change a (e.symm (σ * τ)) = _
    rw [map_mul, ha]
    rfl
  have hs' (σ : Gal(K/k)) (t : K) (v : index → K) :
      ψ σ (t • v) = σ t • ψ σ v := by
    funext i
    exact map_mul σ t (v i)
  have he' (σ : Gal(K/k)) (x : N n) :
      (red ⟨ρ' σ x, stable (e.symm σ) x⟩).toAdd = ψ σ (red x).toAdd := by
    funext i
    exact (he (e.symm σ) x i).trans (congrArg (fun τ : Gal(K/k) => τ ((red x).toAdd i))
      (e.apply_symm_apply σ))
  obtain ⟨d, hd⟩ := semilinearLayerCorrection ρ' (N n) (N (n + 1))
    (fun σ => stable (e.symm σ)) red hs hk ψ hs' he' a' ha' (fun σ => hmem (e.symm σ))
  refine ⟨d, fun σ => ?_⟩
  have h := hd (e σ)
  simpa only [a', ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using h

end Filtration

section Face

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf V : Type u} {J : Type v} [Group G] [Group Wf]
  [AddCommGroup V] [Module ℚ V] {j : G →* FieldPoints M K}
  {A : ApartmentRoots ℚ V J} {p : V} {C : LocalComparison (j := j) (Wf := Wf) A p}

theorem parahoricPreserved (X : Building C) (T : Set (A.SimpleWall p))
    {s : MulAut G} (hs : AutomorphismComparison C s 1) :
    ∀ g ∈ parahoric C T, s g ∈ parahoric C T := by
  obtain ⟨hI, _, _, _, _, _, _, hlift⟩ := hs
  have hT₀ : C.T₀ ≤ parahoric C T := by
    rw [← X.iwahori_inter_normalizer]
    exact fun g hg => Subgroup.subset_closure (Or.inl hg.1)
  change parahoric C T ≤ (parahoric C T).comap s.toMonoidHom
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | ⟨a, ha, rfl⟩)
  · change s g ∈ parahoric C T
    have hi : s g ∈ C.I := by
      rw [← hI]
      exact Subgroup.mem_map.mpr ⟨_, hg, rfl⟩
    exact Subgroup.subset_closure (Or.inl hi)
  · let w := C.coxeter.coxeter.simple a
    change s (C.lift w : G) ∈ parahoric C T
    obtain ⟨v, hv, hmem⟩ := hlift w
    have hvw : v = w := Subtype.ext (by simpa using hv)
    subst v
    have hsimple : (C.lift w : G) ∈ parahoric C T :=
      Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩)
    have hh := (parahoric C T).mul_mem (hT₀ hmem) hsimple
    simpa only [inv_mul_cancel_right] using hh

/-- The face subgroup is compact as a finite union of double cosets of
the compact marked Iwahori. -/
theorem isCompactParahoric [TopologicalSpace G] [ContinuousMul G]
    (X : Building C) (T : Set (A.SimpleWall p)) (hT : T ≠ Set.univ)
    (hI : IsCompact (C.I : Set G)) : IsCompact (parahoric C T : Set G) := by
  let := X.realization.finite_wall_group T hT
  rw [show (parahoric C T : Set G) = _ from X.realization.face_union T]
  exact isCompact_iUnion fun w => by
    rw [DoubleCoset.doubleCoset_eq_image2, ← Set.image_uncurry_prod]
    exact (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)

private theorem rationalWallValue (r : RealCoordinates V) (a : J × ℤ) (x : V) :
    realWallValue A r a (rationalPoint r x) = (A.root a.1 x : ℝ) + (a.2 : ℝ) := by
  simp only [ExceptionalRealAlcove.realWallValue, ExceptionalRealAlcove.rationalPoint,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul, Rat.smul_def, mul_one]

/-- A signed affine root strictly positive at a point of the closed alcove
is positive at its interior basepoint. -/
theorem positiveAtBaseOfPositiveAtFace (X : Building C)
    (t : Weights (A.SimpleWall p)) (x : V)
    (hx : rationalPoint X.realization.coordinates x =
      simplexPoint X.realization.coordinates X.realization.vertex t)
    (a : J × ℤ) (ha : A.positive x a) : A.positive p a := by
  have hcl := congrArg (fun s : Set (EuclideanApartment V) =>
    rationalPoint X.realization.coordinates x ∈ s) X.realization.closed_alcove
  have hnonneg (b : J × ℤ) (hb : A.positive p b) : 0 ≤ A.wallValue b x := by
    have h := (Iff.of_eq hcl).mp ⟨t, hx.symm⟩ b hb
    rw [rationalWallValue] at h
    exact_mod_cast h
  by_contra hp
  let c := C.coxeter
  letI := c.action
  have hop : A.positive p (c.walls.opposite a) := by
    rw [← c.positive_eq]
    exact (c.walls.opposite_positive a).mpr (by simpa only [c.positive_eq] using hp)
  have hneg : A.wallValue (c.walls.opposite a) x = -A.wallValue a x := by
    -- The existence of the negative root follows from the definition of opposite
    -- and the opposite sign rule for the regular basepoint at all integral levels.
    rw [show c.walls.opposite a = A.opposite a from congrFun c.opposite_eq a]
    classical
    change A.value (A.opposite a) x = -A.value a x
    unfold Arithmetic.AffineArrangement.Datum.opposite
    split
    · rename_i h
      change A.root h.choose x + ((-a.2 : ℤ) : ℚ) = -(A.root a.1 x + (a.2 : ℚ))
      rw [h.choose_spec, LinearMap.neg_apply, Int.cast_neg]
      ring
    · rename_i h
      have hpos (b : J × ℤ) : A.positive p (A.opposite b) ↔ ¬A.positive p b := by
        simpa only [c.positive_eq, c.opposite_eq] using c.walls.opposite_positive b
      have hzero := hpos (a.1, 0)
      have hnone : ¬∃ i, A.root i = -A.root (a.1, (0 : ℤ)).1 := h
      unfold Arithmetic.AffineArrangement.Datum.opposite at hzero
      rw [dite_eq_right hnone] at hzero
      simp only [neg_zero] at hzero
      exact (iff_not_self hzero).elim
  have h := hnonneg (c.walls.opposite a) hop
  rw [hneg] at h
  exact (not_lt_of_ge (neg_nonneg.mp h)) ha

end Face

section FaceThreshold

open WithZero

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf V : Type u} {J : Type v} [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
  {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := Wf) A p}

/-- Strictly positive scaled depth at the rational face point implies the
original Iwahori threshold on the relative parameter. -/
theorem scaledDepthOfParameterAtAlcove (Y : Building C) (t : Weights (A.SimpleWall p)) (x : V)
    (hx : rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t)
    (i : J) (s e : ℤ) (he : 0 < e) (hs : (s : ℚ) = (e : ℚ) * A.root i x)
    (r : ℤᵐ⁰) (hr : exp (-s) * r ^ e < 1) :
    r ≤ exp (-threshold (A.root i p)) := by
  rcases eq_or_ne r 0 with rfl | hz
  · simp
  let m := -log r
  have hm : exp (-m) = r := by simpa only [m, neg_neg] using exp_log hz
  have ht : exp (-s) * r ^ e = exp (-(s + e * m)) := by
    rw [← hm, ← exp_zsmul, ← exp_add]
    congr 1
    rw [zsmul_eq_mul]
    simp only [Int.cast_id]
    ring
  rw [ht, exp_lt_one_iff] at hr
  have hm' : (0 : ℚ) < (s : ℚ) + (e : ℚ) * (m : ℚ) := by exact_mod_cast (by omega : 0 < s + e * m)
  have he' : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he
  have hwall : A.positive x (i, m) := by
    change 0 < A.root i x + (m : ℚ)
    apply pos_of_mul_pos_left _ he'.le
    rw [mul_comm, mul_add, ← hs]
    exact hm'
  have hpw := positiveAtBaseOfPositiveAtFace Y t x hx (i, m) hwall
  have hf : ⌊-A.root i p⌋ < m := (Int.floor_lt).mpr (by
    change 0 < A.root i p + (m : ℚ) at hpw
    linarith)
  rw [← hm, exp_le_exp]
  unfold threshold
  omega

end FaceThreshold

section AbsoluteChart

open Opposite
open CategoryTheory.CartesianMonoidalCategory
open IntegralSemisimpleModel
open ExceptionalIwahoriCongruence
open OrderedRootProducts (Enumerates)

universe u

/-- An open chart containing the closed point contains the entire local point. -/
theorem liftLocalChart : LocalChartLifting.{u} := by
  intro R _ X Y c hc p
  constructor
  · rintro ⟨z, hz, _⟩
    exact ⟨changeRing (residueHom R) z, by rw [← hz]; simp [changeRing]⟩
  · rintro ⟨z, hz⟩
    let f : Spec (CommRingCat.of R) ⟶ Y.left := p.left
    have hpt : (integralSpec.map (residueHom R).op).left
        (IsLocalRing.closedPoint (residueRing R)) = IsLocalRing.closedPoint R := by
      change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
        (IsLocalRing.closedPoint (residueRing R)) = IsLocalRing.closedPoint R
      letI : IsLocalHom (IsLocalRing.residue R) :=
        IsLocalHom.of_surjective _ (IsLocalRing.residue_surjective (R := R))
      exact Spec_closedPoint
    have hzpt := congrArg (fun q : integralSpec.obj (op (residueRing R)) ⟶ Y =>
      q.left (IsLocalRing.closedPoint (residueRing R))) hz
    change c.left (z.left (IsLocalRing.closedPoint (residueRing R))) =
      f ((integralSpec.map (residueHom R).op).left (IsLocalRing.closedPoint (residueRing R))) at hzpt
    rw [hpt] at hzpt
    have hrange : Set.range f ⊆ Set.range c.left := by
      rintro _ ⟨x, rfl⟩
      change f x ∈ (c.left.opensRange : Set Y.left)
      exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open
        c.left.opensRange.2 (by rw [c.left.coe_opensRange]; exact ⟨_, hzpt⟩)
    let l : (integralSpec.obj (op R)).left ⟶ X.left :=
      IsOpenImmersion.lift c.left f hrange
    have hl : l ≫ c.left = p.left := IsOpenImmersion.lift_fac _ _ _
    let q : integralSpec.obj (op R) ⟶ X := Over.homMk l (by
      have hw := c.w
      calc
        l ≫ X.hom = l ≫ (c.left ≫ Y.hom) := congrArg (fun h => l ≫ h) hw.symm
        _ = (l ≫ c.left) ≫ Y.hom := (Category.assoc ..).symm
        _ = p.left ≫ Y.hom := congrArg (fun h => h ≫ Y.hom) hl
        _ = (integralSpec.obj (op R)).hom := p.w)
    refine ⟨q, Over.OverMorphism.ext hl, ?_⟩
    intro w hw
    apply Over.OverMorphism.ext
    rw [← cancel_mono c.left]
    exact (congrArg Over.Hom.left hw).trans hl.symm

private theorem additiveCoordinates (R : IntegralAlgebra.{u}) :
    Function.Bijective (additivePoint R) := by
  let φ := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).homEquiv
    (X := op R) (Y := op (CommAlgCat.of Integers.{u} (Polynomial Integers.{u})))
  change Function.Bijective
    (fun t : R => φ (CommAlgCat.ofHom (Polynomial.aeval t)).op)
  refine ⟨?_, ?_⟩
  · intro a b h
    have h' := congrArg (fun f => f.unop.hom Polynomial.X) (φ.injective h)
    simpa using h'
  · intro q
    let f := (φ.symm q).unop.hom
    refine ⟨f Polynomial.X, φ.eq_symm_apply.mp ?_⟩
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    change Polynomial.aeval (f Polynomial.X) = f
    exact Polynomial.algHom_ext (Polynomial.aeval_X _)

private theorem torusCoordinates (D : BasedRootDatum.{u}) (R : IntegralAlgebra.{u}) :
    Function.Bijective (torusPoint D R) := by
  let H := Multiplicative D.X
  let φ := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).homEquiv
    (X := op R) (Y := op (CommAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} H)))
  change Function.Bijective
    (fun t : H →* Rˣ => φ (CommAlgCat.ofHom
      (MonoidAlgebra.lift Integers.{u} R H ((Units.coeHom R).comp t))).op)
  refine ⟨?_, ?_⟩
  · intro a b h
    apply MonoidHom.ext
    intro m
    apply Units.ext
    have h' := congrArg (fun f => f.unop.hom (MonoidAlgebra.of Integers.{u} H m))
      (φ.injective h)
    simpa only [Quiver.Hom.unop_op, CommAlgCat.hom_ofHom, MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] using h'
  · intro q
    let f := (φ.symm q).unop.hom
    let t := (f.toMonoidHom.comp (MonoidAlgebra.of Integers.{u} H)).toHomUnits
    refine ⟨t, φ.eq_symm_apply.mp ?_⟩
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    change MonoidAlgebra.lift Integers.{u} R H ((Units.coeHom R).comp t) = f
    exact (MonoidAlgebra.lift Integers.{u} R H).apply_symm_apply f

private theorem rootValueCoordinates {I : Type u} (L : AdditiveLine.{u})
    (R : IntegralAlgebra.{u}) (l : List I) : Function.Bijective (rootValuePoint L R l) := by
  induction l with
  | nil =>
    refine ⟨fun a b _ => funext (fun i => Fin.elim0 i), fun q => ⟨Fin.elim0, ?_⟩⟩
    exact toUnit_unique _ _
  | cons i l ih =>
    refine ⟨?_, ?_⟩
    · intro a b h
      have h₁ := congrArg (fun p => p ≫ fst _ _) h
      have h₂ := congrArg (fun p => p ≫ snd _ _) h
      simp only [rootValuePoint, lift_fst, lift_snd] at h₁ h₂
      have hzero := (additiveCoordinates R).1 h₁
      have htail := ih.1 h₂
      funext i
      refine Fin.cases hzero (fun j => congrFun htail j) i
    · intro q
      obtain ⟨a, ha⟩ := (additiveCoordinates R).2 (q ≫ fst _ _)
      obtain ⟨b, hb⟩ := ih.2 (q ≫ snd _ _)
      refine ⟨Fin.cons a b, ?_⟩
      change lift (additivePoint R a) (rootValuePoint L R l b) = _
      rw [ha, hb]
      exact lift_comp_fst_snd q

private theorem cellValueCoordinates {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I) :
    Function.Bijective (cellValuePoint M.line R negative positive) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    have h₁ := congrArg (fun f => f ≫ fst _ _) h
    have h₂ := congrArg (fun f => (f ≫ snd _ _) ≫ fst _ _) h
    have h₃ := congrArg (fun f => (f ≫ snd _ _) ≫ snd _ _) h
    simp only [cellValuePoint, lift_fst, lift_snd] at h₁ h₂ h₃
    exact Prod.ext ((rootValueCoordinates _ _ _).1 h₁)
      (Prod.ext ((torusCoordinates _ _).1 h₂) ((rootValueCoordinates _ _ _).1 h₃))
  · intro q
    obtain ⟨a, ha⟩ := (rootValueCoordinates M.line R negative).2 (q ≫ fst _ _)
    obtain ⟨b, hb⟩ := (torusCoordinates D R).2 ((q ≫ snd _ _) ≫ fst _ _)
    obtain ⟨c, hc⟩ := (rootValueCoordinates M.line R positive).2 ((q ≫ snd _ _) ≫ snd _ _)
    refine ⟨(a, b, c), ?_⟩
    change lift (rootValuePoint M.line R negative a)
      (lift (torusPoint D R b) (rootValuePoint M.line R positive c)) = _
    rw [ha, hb, hc, lift_comp_fst_snd, lift_comp_fst_snd]

private theorem additivePoint_map {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (a : R) :
    integralSpec.map f.op ≫ additivePoint R a = additivePoint S (f.hom a) := by
  unfold additivePoint
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  exact Polynomial.algHom_ext (by simp [CommAlgCat.hom_comp])

private theorem torusPoint_map {D : BasedRootDatum.{u}} {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (t : TorusValues D R) :
    integralSpec.map f.op ≫ torusPoint D R t =
      torusPoint D S ((Units.map f.hom.toMonoidHom).comp t) := by
  change integralSpec.map f.op ≫ integralSpec.map (CommAlgCat.ofHom
    (MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X) ((Units.coeHom R).comp t))).op =
    integralSpec.map (CommAlgCat.ofHom (MonoidAlgebra.lift Integers.{u} S (Multiplicative D.X)
      ((Units.coeHom S).comp ((Units.map f.hom.toMonoidHom).comp t)))).op
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext
  · intro m
    change f.hom (MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
      ((Units.coeHom R).comp t) (MonoidAlgebra.of Integers.{u} _ m)) =
      MonoidAlgebra.lift Integers.{u} S (Multiplicative D.X)
        ((Units.coeHom S).comp ((Units.map f.hom.toMonoidHom).comp t))
        (MonoidAlgebra.of Integers.{u} _ m)
    simp only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply]
    rfl
  · exact Subsingleton.elim _ _

private theorem rootValuePoint_map {I : Type u} (L : AdditiveLine.{u})
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List I) (a : Fin l.length → R) :
    integralSpec.map f.op ≫ rootValuePoint L R l a =
      rootValuePoint L S l (fun i => f.hom (a i)) := by
  induction l with
  | nil =>
    exact @toUnit_unique IntegralScheme _ _ (integralSpec.obj (op S)) _ _
  | cons i l ih =>
    change integralSpec.map f.op ≫ lift (additivePoint R (a 0))
      (rootValuePoint L R l (Fin.tail a)) = lift (additivePoint S (f.hom (a 0)))
      (rootValuePoint L S l (fun i => f.hom (a i.succ)))
    rw [comp_lift, additivePoint_map, ih]
    rfl

/-- The marked big-cell coordinates are faithful over all test rings and
commute with their change of scalars. -/
theorem markedCellChart : MarkedChart.{u} := by
  intro D M negative positive hn hp
  constructor
  · intro R a b hab
    apply (cellValueCoordinates M R negative positive).1
    let c := cellMap M.line M.torus M.root negative positive
    haveI : IsOpenImmersion c.left := M.openCell _ _ hn hp
    have hc : Mono c := by
      constructor
      intro Z f g he
      apply Over.OverMorphism.ext
      rw [← cancel_mono c.left]
      exact congrArg Over.Hom.left he
    exact (cancel_mono c).mp hab
  · intro R S f z
    unfold changeRing cellValue cellValuePoint
    rw [← Category.assoc]
    simp only [comp_lift, rootValuePoint_map, torusPoint_map]
    rfl

open IntegralRootRelations in
private def markedRootHom {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (i : D.I) : Multiplicative R →* IntegralPoints M.group R where
  toFun x := M.line.point R x.toAdd ≫ (M.root i).hom.hom
  map_one' := by
    change M.line.point R (0 : R) ≫ (M.root i).hom.hom = 1
    rw [← M.rankOneUpper]
    have h : upper (0 : R) = 1 := by
      apply Subtype.ext
      ext x y
      fin_cases x <;> fin_cases y <;> simp [upper]
    rw [h]
    exact map_one ((M.rankOne i).app R).hom
  map_mul' a b := by
    change M.line.point R (a.toAdd + b.toAdd) ≫ (M.root i).hom.hom = _
    rw [← M.rankOneUpper]
    change (M.rankOne i).app R (upper (a.toAdd + b.toAdd)) =
      (M.line.point R a.toAdd ≫ (M.root i).hom.hom) *
        (M.line.point R b.toAdd ≫ (M.root i).hom.hom)
    rw [← M.rankOneUpper, ← M.rankOneUpper]
    have h : upper (a.toAdd + b.toAdd) = upper a.toAdd * upper b.toAdd := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul]
      ext x y
      fin_cases x <;> fin_cases y <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
    rw [h]
    exact map_mul ((M.rankOne i).app R).hom _ _

private abbrev includeTorus {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) :
    IntegralPoints (splitTorus D) R →* IntegralPoints M.group R :=
  ((yonedaGrp.map M.torus).app (op (integralSpec.obj (op R)))).hom

open WithConv in
private theorem torusPoint_mul {D : BasedRootDatum.{u}} (R : IntegralAlgebra.{u})
    (s t : TorusValues D R) :
    torusPoint D R (s * t) = torusPoint D R s * torusPoint D R t := by
  let A := MonoidAlgebra Integers.{u} (Multiplicative D.X)
  let φ : WithConv (A →ₐ[Integers.{u}] R) ≃* IntegralPoints (splitTorus D) R :=
    Spec.mapMulEquiv
  let f (v : TorusValues D R) : WithConv (A →ₐ[Integers.{u}] R) :=
    toConv (MonoidAlgebra.lift Integers.{u} R _ ((Units.coeHom R).comp v))
  change φ (f (s * t)) = φ (f s) * φ (f t)
  rw [← map_mul]
  apply congrArg φ
  apply WithConv.ofConv_injective
  apply MonoidAlgebra.algHom_ext
  · intro m
    let x := MonoidAlgebra.of Integers.{u} (Multiplicative D.X) m
    change f (s * t) x = (f s * f t) x
    have hx : Coalgebra.comul (R := Integers.{u}) x = x ⊗ₜ[Integers.{u}] x := by
      change Coalgebra.comul (MonoidAlgebra.single m (1 : Integers.{u})) = _
      rw [MonoidAlgebra.comul_single]
      rfl
    rw [AlgHom.convMul_apply, hx]
    change MonoidAlgebra.lift Integers.{u} R _ ((Units.coeHom R).comp (s * t)) x =
      MonoidAlgebra.lift Integers.{u} R _ ((Units.coeHom R).comp s) x *
      MonoidAlgebra.lift Integers.{u} R _ ((Units.coeHom R).comp t) x
    simp only [x, MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply]
    rfl
  · exact Subsingleton.elim _ _

private theorem torusPoint_one {D : BasedRootDatum.{u}} (R : IntegralAlgebra.{u}) :
    torusPoint D R (1 : TorusValues D R) = 1 := by
  have h := torusPoint_mul R (1 : TorusValues D R) 1
  rw [one_mul (1 : TorusValues D R)] at h
  exact mul_right_cancel (h.symm.trans (one_mul _).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem rootValueWord {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (z : Fin l.length → R) :
    rootValuePoint M.line R l z ≫ rootProduct M.line M.root l =
      (List.ofFn fun i : Fin l.length => markedRootHom M R l[i] (Multiplicative.ofAdd (z i))).prod := by
  induction l with
  | nil => rw [rootProduct, MonObj.comp_one]; rfl
  | cons i l ih =>
    rw [rootProduct, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
      List.ofFn_succ, List.prod_cons]
    simp only [rootValuePoint, lift_fst, lift_snd]
    rw [ih]
    rfl

private theorem cellValue_word {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (z : CellValues D R negative positive) :
    cellValue M R negative positive z =
      (List.ofFn fun i : Fin negative.length =>
        markedRootHom M R negative[i] (Multiplicative.ofAdd (z.1 i))).prod *
      (includeTorus M R (torusPoint D R z.2.1) *
      (List.ofFn fun i : Fin positive.length =>
        markedRootHom M R positive[i] (Multiplicative.ofAdd (z.2.2 i))).prod) := by
  rw [cellValue, cellMap, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
  simp only [cellValuePoint, lift_fst, lift_snd]
  rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd, rootValueWord, rootValueWord]
  rfl

private theorem rootValueWord_zero {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) :
    (List.ofFn (fun i : Fin l.length => markedRootHom M R l[i] 1)).prod = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.ofFn_succ, List.prod_cons, map_one, one_mul]
    exact ih

theorem cellValue_one {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I) :
    cellValue M R negative positive (0, 1, 0) = 1 := by
  rw [cellValue_word]
  change (List.ofFn (fun i : Fin negative.length => markedRootHom M R negative[i] 1)).prod *
    (includeTorus M R (torusPoint D R 1) *
      (List.ofFn (fun i : Fin positive.length => markedRootHom M R positive[i] 1)).prod) = 1
  rw [rootValueWord_zero, rootValueWord_zero, torusPoint_one, map_one, one_mul, one_mul]

private theorem scaleRootWord {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (t : TorusValues D R)
    (l : List D.I) (z : Fin l.length → R) :
    MulAut.conj (includeTorus M R (torusPoint D R t))
        (List.ofFn fun i : Fin l.length => markedRootHom M R l[i] (Multiplicative.ofAdd (z i))).prod =
      (List.ofFn fun i : Fin l.length => markedRootHom M R l[i] (Multiplicative.ofAdd
        ((t (Multiplicative.ofAdd (D.datum.root l[i])) : R) * z i))).prod := by
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact M.conjugation R t l[i] (z i)

/-- Scaling the marked point by a split torus element scales its marked root slots. -/
theorem scaleMarkedCell : ScaleMarkedChart.{u} := by
  intro D M R negative positive t z
  let s := includeTorus M R (torusPoint D R t)
  have htor : MulAut.conj s (includeTorus M R (torusPoint D R z.2.1)) =
      includeTorus M R (torusPoint D R z.2.1) := by
    let a := includeTorus M R (torusPoint D R z.2.1)
    have h : s * a = a * s := by
      change includeTorus M R (torusPoint D R t) * includeTorus M R (torusPoint D R z.2.1) =
        includeTorus M R (torusPoint D R z.2.1) * includeTorus M R (torusPoint D R t)
      rw [← map_mul, ← map_mul, ← torusPoint_mul, ← torusPoint_mul, mul_comm t]
    change s * a * s⁻¹ = a
    rw [h, mul_inv_cancel_right]
  rw [cellValue_word, cellValue_word]
  change MulAut.conj s (_ * (_ * _)) = _
  rw [map_mul, map_mul, scaleRootWord, scaleRootWord, htor]
  rfl

private theorem congruenceHom_comp_residue {R : IntegralAlgebra.{u}} [IsLocalRing R]
    {n : ℕ} (hn : 0 < n) :
    ∃ f : congruenceRing R n ⟶ residueRing R, congruenceHom R n ≫ f = residueHom R := by
  let I := IsLocalRing.maximalIdeal R
  let f := Ideal.Quotient.factorₐ Integers.{u} (Ideal.pow_le_self (n := n) (by omega) : I ^ n ≤ I)
  exact ⟨CommAlgCat.ofHom f, rfl⟩

/-- The full marked cell tests congruence to identity through every positive
power of the maximal ideal, including powers with nonreduced quotient. -/
theorem markedIdentityCongruence {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) [IsLocalRing R] (negative positive : List D.I)
    (hneg : Enumerates negative {i | ¬ D.base.IsPos i})
    (hpos : Enumerates positive {i | D.base.IsPos i})
    {n : ℕ} (hn : 0 < n) (g : IntegralPoints M.group R) :
    changeRingHom M.group (congruenceHom R n) g = 1 ↔
      ∃! z : CellValues D R negative positive, cellValue M R negative positive z = g ∧
        (∀ i, z.1 i ∈ IsLocalRing.maximalIdeal R ^ n) ∧
        (∀ χ, (z.2.1 χ : R) - 1 ∈ IsLocalRing.maximalIdeal R ^ n) ∧
        ∀ i, z.2.2 i ∈ IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨hinj, hmap⟩ := markedCellChart M negative positive hneg hpos
  have hcoords (z : CellValues D R negative positive) :
      changeRingHom M.group (congruenceHom R n) (cellValue M R negative positive z) = 1 ↔
      (∀ i, z.1 i ∈ IsLocalRing.maximalIdeal R ^ n) ∧
      (∀ χ, (z.2.1 χ : R) - 1 ∈ IsLocalRing.maximalIdeal R ^ n) ∧
      ∀ i, z.2.2 i ∈ IsLocalRing.maximalIdeal R ^ n := by
    change changeRing (congruenceHom R n) (cellValue M R negative positive z) = 1 ↔ _
    rw [hmap, ← cellValue_one M (congruenceRing R n) negative positive,
      (hinj _).eq_iff, Prod.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      refine ⟨fun i => Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h₁ i),
        fun χ => Ideal.Quotient.eq.mp ?_,
        fun i => Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h₃ i)⟩
      rw [map_one]
      exact congrArg (fun t : TorusValues D (congruenceRing R n) =>
        ((t χ : (congruenceRing R n)ˣ) : congruenceRing R n)) h₂
    · rintro ⟨h₁, h₂, h₃⟩
      refine ⟨funext (fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (h₁ i)), ?_,
        funext (fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (h₃ i))⟩
      exact MonoidHom.ext (fun χ => Units.ext (Ideal.Quotient.eq.mpr (h₂ χ)))
  constructor
  · intro hg
    obtain ⟨f, hf⟩ := congruenceHom_comp_residue (R := R) hn
    have hred : changeRingHom M.group (residueHom R) g = 1 := by
      rw [← hf]
      change (((integralPointFunctor M.group).map (congruenceHom R n ≫ f)).hom) g = 1
      rw [Functor.map_comp]
      change changeRingHom M.group f (changeRingHom M.group (congruenceHom R n) g) = 1
      rw [hg, map_one]
    let c := cellMap M.line M.torus M.root negative positive
    letI : IsOpenImmersion c.left := M.openCell negative positive hneg hpos
    obtain ⟨p, hp, _⟩ := (liftLocalChart R c g).mpr
      ⟨cellValuePoint M.line _ negative positive (0, 1, 0),
        (cellValue_one M _ negative positive).trans hred.symm⟩
    obtain ⟨z, rfl⟩ := (cellValueCoordinates M R negative positive).2 p
    change cellValue M R negative positive z = g at hp
    refine ⟨z, ⟨hp, (hcoords z).mp (by rwa [hp])⟩,
      fun v hv => hinj R (hv.1.trans hp.symm)⟩
  · rintro ⟨z, ⟨rfl, hz⟩, _⟩
    exact (hcoords z).mpr hz

private theorem chartOfScalarExtension {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (hf : Function.Surjective (integralSpec.map f.op).left)
    {X Y : IntegralScheme.{u}} (c : X ⟶ Y) [IsOpenImmersion c.left]
    (p : integralSpec.obj (op R) ⟶ Y)
    (w : integralSpec.obj (op S) ⟶ X) (hw : w ≫ c = changeRing f p) :
    ∃ z : integralSpec.obj (op R) ⟶ X, z ≫ c = p := by
  have hrange : Set.range p.left ⊆ Set.range c.left := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨r, rfl⟩ := hf q
    have h := congrArg (fun q : integralSpec.obj (op S) ⟶ Y => q.left r) hw
    exact ⟨w.left r, h⟩
  let l : (integralSpec.obj (op R)).left ⟶ X.left :=
    IsOpenImmersion.lift c.left p.left hrange
  have hl : l ≫ c.left = p.left := IsOpenImmersion.lift_fac _ _ _
  use Over.homMk l (by
    calc
      l ≫ X.hom = l ≫ (c.left ≫ Y.hom) := congrArg (fun h => l ≫ h) c.w.symm
      _ = (l ≫ c.left) ≫ Y.hom := (Category.assoc ..).symm
      _ = p.left ≫ Y.hom := congrArg (fun h => h ≫ Y.hom) hl
      _ = (integralSpec.obj (op R)).hom := p.w)
  exact Over.OverMorphism.ext hl

private theorem unscaleCell {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I) (t : TorusValues D R)
    (z : CellValues D R negative positive) :
    (MulAut.conj (includeTorus M R (torusPoint D R t))).symm
        (cellValue M R negative positive z) =
      cellValue M R negative positive (scaleCellValues t⁻¹ z) := by
  have h : torusPoint D R t⁻¹ = (torusPoint D R t)⁻¹ := by
    have hmul := torusPoint_mul R t⁻¹ t
    rw [inv_mul_cancel t, torusPoint_one] at hmul
    exact eq_inv_of_mul_eq_one_left hmul.symm
  have he := scaleMarkedCell M R negative positive t⁻¹ z
  change MulAut.conj (includeTorus M R (torusPoint D R t⁻¹)) _ = _ at he
  rw [h, map_inv, map_inv, MulAut.inv_apply] at he
  exact he

private theorem changeRing_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (changeRingHom M.group f) := by
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr M.affine
  intro p q he
  obtain ⟨a, rfl⟩ := (pointAlgebraEquiv B.unop e R).surjective p
  obtain ⟨b, rfl⟩ := (pointAlgebraEquiv B.unop e R).surjective q
  have h (a : B.unop →ₐ[Integers.{u}] R) :
      changeRingHom M.group f (pointAlgebraEquiv B.unop e R a) =
        pointAlgebraEquiv B.unop e S (f.hom.comp a) := by
    change integralSpec.map f.op ≫ (integralSpec.map (CommAlgCat.ofHom a).op ≫ e.hom) =
      integralSpec.map (CommAlgCat.ofHom (f.hom.comp a)).op ≫ e.hom
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
    rfl
  rw [h, h] at he
  have hc := (pointAlgebraEquiv B.unop e S).injective he
  exact congrArg (pointAlgebraEquiv B.unop e R) (AlgHom.ext fun x => hf (congrFun (congrArg
    (fun a : B.unop →ₐ[Integers.{u}] S => (a : B.unop → S)) hc) x))

/-- A scaled lift that is congruent to identity has a unique marked chart
before scaling and exactly the indicated congruence bounds afterwards. -/
theorem scaledIdentityCongruence {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S O : IntegralAlgebra.{u}} [IsLocalRing O]
    (f : R ⟶ S) (hf : Function.Surjective (integralSpec.map f.op).left)
    (i : O ⟶ S) (hi : Function.Injective i.hom)
    (negative positive : List D.I)
    (hneg : Enumerates negative {a | ¬ D.base.IsPos a})
    (hpos : Enumerates positive {a | D.base.IsPos a})
    (t : TorusValues D S) (p : IntegralPoints M.group R) (q : IntegralPoints M.group O)
    (hq : changeRingHom M.group i q =
      MulAut.conj (includeTorus M S (torusPoint D S t)) (changeRingHom M.group f p))
    {n : ℕ} (hn : 0 < n) :
    changeRingHom M.group (congruenceHom O n) q = 1 ↔
      ∃! z : CellValues D R negative positive, cellValue M R negative positive z = p ∧
        ∃ w : CellValues D O negative positive,
          mapCellValues i w = scaleCellValues t (mapCellValues f z) ∧
          (∀ j, w.1 j ∈ IsLocalRing.maximalIdeal O ^ n) ∧
          (∀ χ, (w.2.1 χ : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ n) ∧
          ∀ j, w.2.2 j ∈ IsLocalRing.maximalIdeal O ^ n := by
  obtain ⟨hinj, hmap⟩ := markedCellChart M negative positive hneg hpos
  have hnq := markedIdentityCongruence M O negative positive hneg hpos hn q
  constructor
  · intro h
    obtain ⟨w, ⟨hw, hneg', htor', hpos'⟩, _⟩ := hnq.mp h
    have hw' : cellValue M S negative positive (mapCellValues i w) =
        MulAut.conj (includeTorus M S (torusPoint D S t)) (changeRing f p) :=
      (hmap i w).symm.trans ((congrArg (changeRingHom M.group i) hw).trans hq)
    have hpre : cellValue M S negative positive (scaleCellValues t⁻¹ (mapCellValues i w)) =
        changeRing f p := by
      rw [← unscaleCell, hw']
      exact MulEquiv.symm_apply_apply _ _
    let c := cellMap M.line M.torus M.root negative positive
    letI : IsOpenImmersion c.left := M.openCell negative positive hneg hpos
    obtain ⟨a, ha⟩ := chartOfScalarExtension f hf c p
      (cellValuePoint M.line S negative positive (scaleCellValues t⁻¹ (mapCellValues i w))) hpre
    obtain ⟨z, rfl⟩ := (cellValueCoordinates M R negative positive).2 a
    change cellValue M R negative positive z = p at ha
    refine ⟨z, ⟨ha, w, ?_, hneg', htor', hpos'⟩, fun a ha' => hinj R (ha'.1.trans ha.symm)⟩
    apply hinj S
    calc
      cellValue M S negative positive (mapCellValues i w) =
          MulAut.conj (includeTorus M S (torusPoint D S t)) (changeRing f p) := hw'
      _ = cellValue M S negative positive (scaleCellValues t (mapCellValues f z)) := by
        exact (congrArg (MulAut.conj (includeTorus M S (torusPoint D S t)))
          ((congrArg (changeRing f) ha.symm).trans (hmap f z))).trans
          (scaleMarkedCell M S negative positive t _)
  · rintro ⟨z, ⟨hz, w, hwi, hneg', htor', hpos'⟩, _⟩
    have hw : cellValue M O negative positive w = q := by
      apply changeRing_injective M i hi
      change changeRing i (cellValue M O negative positive w) = _
      rw [hmap, hwi, ← scaleMarkedCell, ← hmap, hz]
      exact hq.symm
    exact hnq.mpr ⟨w, ⟨hw, hneg', htor', hpos'⟩,
      fun a ha => hinj O (ha.1.trans hw.symm)⟩

end AbsoluteChart

section SquareZero

open Opposite WithConv
open IntegralSemisimpleModel ExceptionalIwahoriCongruence
open OrderedRootProducts (Enumerates)
open scoped RingTheory.LinearMap

universe u

private theorem specPoint_natural {A : Type u} [CommRing A] [HopfAlgebra Integers.{u} A]
    {S T : IntegralAlgebra.{u}} (f : S ⟶ T) (p : WithConv (A →ₐ[Integers.{u}] S)) :
    let G := (hopfSpec (CommRingCat.of Integers.{u})).obj
      (op (CommHopfAlgCat.of Integers.{u} A))
    (Spec.mapMulEquiv (toConv (f.hom.comp p.ofConv)) : IntegralPoints G T) =
      changeRingHom G f (Spec.mapMulEquiv p) := by
  intro G
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (f.hom.comp p.ofConv).toRingHom) =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ Spec.map (CommRingCat.ofHom p.ofConv.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem convolution_difference_product {B A R : Type*} [CommRing B]
    [CommRing A] [Bialgebra B A] [CommRing R] [Algebra B R]
    (I : Ideal R) (hI : I ^ 2 = ⊥) {p q : A →ₗ[B] R}
    (hp : ∀ x, p x ∈ I) (hq : ∀ x, q x ∈ I) :
    (toConv p * toConv q : WithConv (A →ₗ[B] R)) = 0 := by
  classical
  apply WithConv.ofConv_injective
  ext x
  change (toConv p * toConv q : WithConv (A →ₗ[B] R)) x = 0
  rw [(Coalgebra.Repr.arbitrary B x).convMul_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hm := Ideal.mul_mem_mul (hp ((Coalgebra.Repr.arbitrary B x).left i))
    (hq ((Coalgebra.Repr.arbitrary B x).right i))
  rw [← pow_two, hI] at hm
  exact hm

/-- On a square-zero ideal the group law on points reducing to identity
adds their differences from the augmentation, on every coordinate function. -/
theorem squareZeroConvolution {B A R : Type*} [CommRing B] [CommRing A] [HopfAlgebra B A]
    [CommRing R] [Algebra B R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (p q : WithConv (A →ₐ[B] R))
    (hp : ∀ x, p x - (1 : WithConv (A →ₐ[B] R)) x ∈ I)
    (hq : ∀ x, q x - (1 : WithConv (A →ₐ[B] R)) x ∈ I) :
    ∀ x, (p * q) x =
      p x + q x - (1 : WithConv (A →ₐ[B] R)) x := by
  let P := toConv p.ofConv.toLinearMap
  let Q := toConv q.ofConv.toLinearMap
  have hmul : (P - 1) * (Q - 1) = 0 :=
    convolution_difference_product I hI
      (p := p.ofConv.toLinearMap - (1 : WithConv (A →ₗ[B] R)).ofConv)
      (q := q.ofConv.toLinearMap - (1 : WithConv (A →ₗ[B] R)).ofConv) hp hq
  have he : P * Q = P + Q - 1 := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul] at hmul
    calc
      P * Q = (P * Q - P - (Q - 1)) + (P + Q - 1) := by abel
      _ = _ := by rw [hmul, zero_add]
  intro x
  exact congrArg (fun z : WithConv (A →ₗ[B] R) => z x) he

/-- Two points reducing to identity across a square-zero quotient commute. -/
theorem squareZeroPointKernelCommutes (G : IntegralGroup.{u}) (hG : IsAffine G.X.left)
    {S T : IntegralAlgebra.{u}} (f : S ⟶ T) (hI : (RingHom.ker f.hom.toRingHom) ^ 2 = ⊥)
    {p q : IntegralPoints G S} (hp : changeRingHom G f p = 1)
    (hq : changeRingHom G f q = 1) : Commute p q := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr hG
  let G₀ := (hopfSpec (CommRingCat.of Integers.{u})).obj A
  let a (R : IntegralAlgebra.{u}) : IntegralPoints G R →* IntegralPoints G₀ R :=
    ((yonedaGrp.map e.inv).app (op (integralSpec.obj (op R)))).hom
  have ha : Function.Injective (a S) := by
    intro x y h
    let e₀ := (Grp.forget IntegralScheme).mapIso e
    change x ≫ e₀.inv = y ≫ e₀.inv at h
    exact (cancel_mono e₀.inv).mp h
  have hanat (x : IntegralPoints G S) :
      changeRingHom G₀ f (a S x) = a T (changeRingHom G f x) := by
    change integralSpec.map f.op ≫ x ≫ e.inv.hom.hom =
      (integralSpec.map f.op ≫ x) ≫ e.inv.hom.hom
    exact (Category.assoc ..).symm
  let φ (R : IntegralAlgebra.{u}) :
      WithConv (A.unop →ₐ[Integers.{u}] R) ≃* IntegralPoints G₀ R := Spec.mapMulEquiv
  let x := (φ S).symm (a S p)
  let y := (φ S).symm (a S q)
  have hk (r : IntegralPoints G S) (hr : changeRingHom G f r = 1) (z : A.unop) :
      ((φ S).symm (a S r)) z - (1 : WithConv (A.unop →ₐ[Integers.{u}] S)) z ∈
        RingHom.ker f.hom.toRingHom := by
    let w := (φ S).symm (a S r)
    have h : toConv (f.hom.comp w.ofConv) = (1 : WithConv (A.unop →ₐ[Integers.{u}] T)) := by
      apply (φ T).injective
      rw [map_one]
      calc
        φ T (toConv (f.hom.comp w.ofConv)) = changeRingHom G₀ f (φ S w) := specPoint_natural f w
        _ = 1 := by rw [show φ S w = a S r from (φ S).apply_symm_apply _, hanat, hr, map_one]
    change f.hom (w z - (1 : WithConv (A.unop →ₐ[Integers.{u}] S)) z) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hz := congrArg (fun g : WithConv (A.unop →ₐ[Integers.{u}] T) => g z) h
    change f.hom (w z) = _ at hz
    simpa only [AlgHom.convOne_apply, AlgHom.commutes] using hz
  have hxy : x * y = y * x := by
    apply WithConv.ofConv_injective
    ext z
    change (x * y) z = (y * x) z
    rw [squareZeroConvolution _ hI x y (hk p hp) (hk q hq),
      squareZeroConvolution _ hI y x (hk q hq) (hk p hp), add_comm (x z)]
  apply ha
  rw [map_mul, map_mul]
  simpa only [map_mul, x, y, MulEquiv.apply_symm_apply] using congrArg (φ S) hxy

private theorem markedRootHom_natural {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S T : IntegralAlgebra.{u}} (f : S ⟶ T) (a : D.I) (x : S) :
    changeRingHom M.group f (markedRootHom M S a (Multiplicative.ofAdd x)) =
      markedRootHom M T a (Multiplicative.ofAdd (f.hom x)) := by
  change integralSpec.map f.op ≫ additivePoint S x ≫ (M.root a).hom.hom = _
  rw [← Category.assoc, additivePoint_map]
  rfl

private theorem includeTorus_natural {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S T : IntegralAlgebra.{u}} (f : S ⟶ T) (t : TorusValues D S) :
    changeRingHom M.group f (includeTorus M S (torusPoint D S t)) =
      includeTorus M T (torusPoint D T ((Units.map f.hom.toMonoidHom).comp t)) := by
  change integralSpec.map f.op ≫ torusPoint D S t ≫ M.torus.hom.hom = _
  rw [← Category.assoc, torusPoint_map]
  rfl

/-- Modulo a square-zero ideal, the marked root coordinates add and the
torus coordinates multiply on the kernel of reduction. -/
theorem squareZeroCellValue_mul {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S T : IntegralAlgebra.{u}} (f : S ⟶ T) (hI : (RingHom.ker f.hom.toRingHom) ^ 2 = ⊥)
    (negative positive : List D.I) (z w : CellValues D S negative positive)
    (hz : mapCellValues f z = (0, 1, 0)) (hw : mapCellValues f w = (0, 1, 0)) :
    cellValue M S negative positive z * cellValue M S negative positive w =
      cellValue M S negative positive (z.1 + w.1, z.2.1 * w.2.1, z.2.2 + w.2.2) := by
  let N := (changeRingHom M.group f).ker
  let groupN : Group N := inferInstance
  letI : CommGroup N :=
    { groupN with
      mul_comm := fun a b => Subtype.ext (squareZeroPointKernelCommutes M.group M.affine f hI a.2 b.2).eq }
  let t (a : TorusValues D S) (ha : (Units.map f.hom.toMonoidHom).comp a = 1) : N :=
    ⟨includeTorus M S (torusPoint D S a), by
      change changeRingHom M.group f (includeTorus M S (torusPoint D S a)) = 1
      rw [includeTorus_natural, ha, torusPoint_one, map_one]⟩
  let r (l : List D.I) (a : Fin l.length → S) (ha : ∀ i, f.hom (a i) = 0) (i : Fin l.length) : N :=
    ⟨markedRootHom M S l[i] (Multiplicative.ofAdd (a i)), by
      change changeRingHom M.group f (markedRootHom M S l[i] (Multiplicative.ofAdd (a i))) = 1
      rw [markedRootHom_natural, ha i]
      exact map_one (markedRootHom M T l[i])⟩
  have hr (l : List D.I) (a b : Fin l.length → S)
      (ha : ∀ i, f.hom (a i) = 0) (hb : ∀ i, f.hom (b i) = 0)
      (hab : ∀ i, f.hom ((a + b) i) = 0) :
      (List.ofFn (r l a ha)).prod * (List.ofFn (r l b hb)).prod =
        (List.ofFn (r l (a + b) hab)).prod := by
    simp only [List.prod_ofFn, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    apply Subtype.ext
    exact (map_mul (markedRootHom M S l[i]) (Multiplicative.ofAdd (a i))
      (Multiplicative.ofAdd (b i))).symm
  have hnz (i : Fin negative.length) : f.hom (z.1 i) = 0 :=
    congrFun (congrArg Prod.fst hz) i
  have hnw (i : Fin negative.length) : f.hom (w.1 i) = 0 :=
    congrFun (congrArg Prod.fst hw) i
  have hpz (i : Fin positive.length) : f.hom (z.2.2 i) = 0 :=
    congrFun (congrArg (fun c => c.2.2) hz) i
  have hpw (i : Fin positive.length) : f.hom (w.2.2 i) = 0 :=
    congrFun (congrArg (fun c => c.2.2) hw) i
  have htz : (Units.map f.hom.toMonoidHom).comp z.2.1 = 1 :=
    congrArg (fun c => c.2.1) hz
  have htw : (Units.map f.hom.toMonoidHom).comp w.2.1 = 1 :=
    congrArg (fun c => c.2.1) hw
  have hns (i : Fin negative.length) : f.hom ((z.1 + w.1) i) = 0 := by
    rw [Pi.add_apply, map_add, hnz, hnw, zero_add]
  have hps (i : Fin positive.length) : f.hom ((z.2.2 + w.2.2) i) = 0 := by
    rw [Pi.add_apply, map_add, hpz, hpw, zero_add]
  have hts : (Units.map f.hom.toMonoidHom).comp (z.2.1 * w.2.1) = 1 := by
    apply MonoidHom.ext
    intro χ
    have hz' : Units.map f.hom.toMonoidHom (z.2.1 χ) = 1 := DFunLike.congr_fun htz χ
    have hw' : Units.map f.hom.toMonoidHom (w.2.1 χ) = 1 := DFunLike.congr_fun htw χ
    change Units.map f.hom.toMonoidHom (z.2.1 χ * w.2.1 χ) = 1
    rw [map_mul, hz', hw', one_mul]
  have htm : t z.2.1 htz * t w.2.1 htw = t (z.2.1 * w.2.1) hts := by
    apply Subtype.ext
    change _ * _ = includeTorus M S (torusPoint D S (z.2.1 * w.2.1))
    rw [torusPoint_mul, map_mul]
  have hprod :
      ((List.ofFn (r negative z.1 hnz)).prod *
        (t z.2.1 htz * (List.ofFn (r positive z.2.2 hpz)).prod)) *
      ((List.ofFn (r negative w.1 hnw)).prod *
        (t w.2.1 htw * (List.ofFn (r positive w.2.2 hpw)).prod)) =
      (List.ofFn (r negative (z.1 + w.1) hns)).prod *
        (t (z.2.1 * w.2.1) hts * (List.ofFn (r positive (z.2.2 + w.2.2) hps)).prod) := by
    rw [← hr negative z.1 w.1 hnz hnw hns, ← hr positive z.2.2 w.2.2 hpz hpw hps, ← htm]
    ac_rfl
  rw [cellValue_word, cellValue_word, cellValue_word]
  simpa only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, r, t, Subgroup.subtype_apply] using
    congrArg (fun x : N => N.subtype x) hprod

private def congruenceTransition (O : IntegralAlgebra.{u}) [IsLocalRing O]
    {m n : ℕ} (h : n ≤ m) : congruenceRing O m ⟶ congruenceRing O n :=
  CommAlgCat.ofHom (Ideal.Quotient.factorₐ Integers.{u}
    (Ideal.pow_le_pow_right h : IsLocalRing.maximalIdeal O ^ m ≤ IsLocalRing.maximalIdeal O ^ n))

private theorem congruenceTransition_sq (O : IntegralAlgebra.{u}) [IsLocalRing O]
    {n : ℕ} (hn : 0 < n) :
    RingHom.ker (congruenceTransition O (Nat.le_succ n)).hom.toRingHom ^ 2 = ⊥ := by
  let I := IsLocalRing.maximalIdeal O
  let f := Ideal.Quotient.mk (I ^ (n + 1))
  change RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)) ^ 2 = ⊥
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

/-- The two positive-depth marked tuples multiply coordinatewise after
truncation at the next depth. -/
theorem congruenceCellValue_mul {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (O : IntegralAlgebra.{u}) [IsLocalRing O] {n : ℕ} (hn : 0 < n)
    (negative positive : List D.I) (z w : CellValues D O negative positive)
    (hz : mapCellValues (congruenceHom O n) z = (0, 1, 0))
    (hw : mapCellValues (congruenceHom O n) w = (0, 1, 0))
    (hneg : Enumerates negative {i | ¬ D.base.IsPos i})
    (hpos : Enumerates positive {i | D.base.IsPos i}) :
    changeRingHom M.group (congruenceHom O (n + 1))
        (cellValue M O negative positive z * cellValue M O negative positive w) =
      changeRingHom M.group (congruenceHom O (n + 1))
        (cellValue M O negative positive (z.1 + w.1, z.2.1 * w.2.1, z.2.2 + w.2.2)) := by
  let f := congruenceHom O (n + 1)
  let q := congruenceTransition O (Nat.le_succ n)
  have hmap (z : CellValues D O negative positive) :
      changeRingHom M.group f (cellValue M O negative positive z) =
        cellValue M _ negative positive (mapCellValues f z) :=
    (markedCellChart M negative positive hneg hpos).2 f z
  change changeRingHom M.group f _ = changeRingHom M.group f _
  rw [map_mul, hmap, hmap, hmap]
  have hm (v : CellValues D O negative positive) :
      mapCellValues q (mapCellValues f v) = mapCellValues (congruenceHom O n) v := by
    apply Prod.ext
    · rfl
    · exact Prod.ext (MonoidHom.ext (fun χ => Units.ext rfl)) rfl
  rw [squareZeroCellValue_mul M q (congruenceTransition_sq O hn) negative positive
    (mapCellValues f z) (mapCellValues f w) ((hm z).trans hz) ((hm w).trans hw)]
  congr 1

end SquareZero

section LeadingCoefficients

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable (π : O) (hπ : maximalIdeal O = Ideal.span {π})
include hπ

omit [IsDomain O] in
private theorem maximalIdeal_pow_eq_span (n : ℕ) :
    maximalIdeal O ^ n = Ideal.span {π ^ n} := by
  rw [hπ, Ideal.span_singleton_pow]

/-- Divide an integral entry by the chosen uniformizer power before reducing.
For a torus coordinate, the entry is the difference from one. -/
def leadingCoefficient (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (n : ℕ) (z : ↥(maximalIdeal O ^ n)) : ResidueField O :=
  residue O (Classical.choose (Ideal.mem_span_singleton.mp
    (show (z : O) ∈ Ideal.span {π ^ n} from
      (maximalIdeal_pow_eq_span π hπ n) ▸ (show (z : O) ∈ maximalIdeal O ^ n from z.2))))

theorem leadingCoefficient_eq_of_factor {n : ℕ} (z : ↥(maximalIdeal O ^ n))
    (hπ₀ : π ≠ 0) {b : O} (hb : (z : O) = π ^ n * b) :
    leadingCoefficient π hπ n z = residue O b := by
  apply congrArg (residue O)
  apply mul_left_cancel₀ (pow_ne_zero n hπ₀)
  have hz : (z : O) ∈ Ideal.span {π ^ n} := by
    rw [← maximalIdeal_pow_eq_span π hπ n]
    exact z.2
  exact (Classical.choose_spec (Ideal.mem_span_singleton.mp hz)).symm.trans hb

omit [IsDomain O] in
private theorem mem_maximalIdeal_pow_iff_factor (n : ℕ) (z : O) :
    z ∈ maximalIdeal O ^ n ↔ ∃ b, z = π ^ n * b := by
  rw [maximalIdeal_pow_eq_span π hπ, Ideal.mem_span_singleton]
  rfl

theorem leadingCoefficient_zero_iff {n : ℕ} (z : ↥(maximalIdeal O ^ n)) (hπ₀ : π ≠ 0) :
    leadingCoefficient π hπ n z = 0 ↔ (z : O) ∈ maximalIdeal O ^ (n + 1) := by
  obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff_factor π hπ n (z : O)).mp z.2
  have h : b ∈ maximalIdeal O ↔ ∃ a, b = π * a := by
    rw [hπ, Ideal.mem_span_singleton]
    rfl
  rw [leadingCoefficient_eq_of_factor π hπ z hπ₀ hb,
    mem_maximalIdeal_pow_iff_factor π hπ (n + 1)]
  change Ideal.Quotient.mk (maximalIdeal O) b = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, h]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [hb, ha, pow_succ, mul_assoc]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, mul_left_cancel₀ (pow_ne_zero n hπ₀) ?_⟩
    rw [← hb, ← mul_assoc, ← pow_succ]
    exact ha

theorem leadingCoefficient_add {n : ℕ} (z w : ↥(maximalIdeal O ^ n)) (hπ₀ : π ≠ 0) :
    leadingCoefficient π hπ n (z + w) =
      leadingCoefficient π hπ n z + leadingCoefficient π hπ n w := by
  obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff_factor π hπ n (z : O)).mp z.2
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_pow_iff_factor π hπ n (w : O)).mp w.2
  have h : ((z + w : ↥(maximalIdeal O ^ n)) : O) = π ^ n * (b + c) := by
    change (z : O) + (w : O) = _
    rw [hb, hc, mul_add]
  rw [leadingCoefficient_eq_of_factor π hπ _ hπ₀ h,
    leadingCoefficient_eq_of_factor π hπ z hπ₀ hb,
    leadingCoefficient_eq_of_factor π hπ w hπ₀ hc, map_add]

theorem leadingCoefficient_surjective (n : ℕ) (hπ₀ : π ≠ 0) :
    Function.Surjective (leadingCoefficient π hπ n) := by
  intro b
  obtain ⟨r, rfl⟩ := residue_surjective (R := O) b
  refine ⟨⟨π ^ n * r, (mem_maximalIdeal_pow_iff_factor π hπ _ _).mpr ⟨r, rfl⟩⟩, ?_⟩
  exact leadingCoefficient_eq_of_factor π hπ _ hπ₀ rfl

theorem leadingCoefficient_map {n : ℕ} (z : ↥(maximalIdeal O ^ n)) (hπ₀ : π ≠ 0)
    (σ : O ≃+* O) (hσ : σ π = π) (w : ↥(maximalIdeal O ^ n)) (hw : (w : O) = σ (z : O)) :
    leadingCoefficient π hπ n w =
      letI := IsLocalHom.of_surjective σ.toRingHom σ.surjective
      ResidueField.map σ.toRingHom (leadingCoefficient π hπ n z) := by
  letI := IsLocalHom.of_surjective σ.toRingHom σ.surjective
  obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff_factor π hπ n (z : O)).mp z.2
  have hw' : (w : O) = π ^ n * σ b := by rw [hw, hb, map_mul, map_pow, hσ]
  rw [leadingCoefficient_eq_of_factor π hπ w hπ₀ hw',
    leadingCoefficient_eq_of_factor π hπ z hπ₀ hb]
  rfl

private def leadingCoefficientHom (hπ₀ : π ≠ 0) (n : ℕ) :
    ↥(maximalIdeal O ^ n) →+ ResidueField O where
  toFun := leadingCoefficient π hπ n
  map_zero' := by
    rw [leadingCoefficient_eq_of_factor π hπ 0 hπ₀ (b := 0) (by simp), map_zero]
  map_add' z w := leadingCoefficient_add π hπ z w hπ₀

theorem leadingCoefficient_eq_iff {n : ℕ} (z w : ↥(maximalIdeal O ^ n)) (hπ₀ : π ≠ 0) :
    leadingCoefficient π hπ n z = leadingCoefficient π hπ n w ↔
      (z : O) - (w : O) ∈ maximalIdeal O ^ (n + 1) := by
  let f := leadingCoefficientHom π hπ hπ₀ n
  change f z = f w ↔ _
  rw [← sub_eq_zero, ← map_sub]
  exact leadingCoefficient_zero_iff π hπ (z - w) hπ₀

/-- Leading torus entries add when multiplying two units close to one. -/
theorem leadingCoefficient_unit_mul {n : ℕ} (hn : 0 < n) (hπ₀ : π ≠ 0)
    (s t : Oˣ) (hs : (s : O) - 1 ∈ maximalIdeal O ^ n)
    (ht : (t : O) - 1 ∈ maximalIdeal O ^ n)
    (hst : ((s * t : Oˣ) : O) - 1 ∈ maximalIdeal O ^ n) :
    leadingCoefficient π hπ n ⟨((s * t : Oˣ) : O) - 1, hst⟩ =
      leadingCoefficient π hπ n ⟨(s : O) - 1, hs⟩ +
        leadingCoefficient π hπ n ⟨(t : O) - 1, ht⟩ := by
  let I := maximalIdeal O
  let a : ↥(I ^ n) := ⟨(s : O) - 1, hs⟩
  let b : ↥(I ^ n) := ⟨(t : O) - 1, ht⟩
  rw [← leadingCoefficient_add π hπ a b hπ₀]
  apply (leadingCoefficient_eq_iff π hπ _ _ hπ₀).mpr
  change (s : O) * (t : O) - 1 - (((s : O) - 1) + ((t : O) - 1)) ∈ I ^ (n + 1)
  rw [show (s : O) * (t : O) - 1 - (((s : O) - 1) + ((t : O) - 1)) =
    ((s : O) - 1) * ((t : O) - 1) by ring]
  have hle : I ^ (n + n) ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  apply hle
  rw [pow_add]
  exact Ideal.mul_mem_mul hs ht

end LeadingCoefficients

section NormalizedDepth

open ValuativeRel WithZero IsLocalRing
open ExceptionalLocalRootCoordinates (normalizedValuation normalizedValueGroupMap)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem normalizedValuation_le_iff (a b : K) :
    normalizedValuation K a ≤ normalizedValuation K b ↔ valuation K a ≤ valuation K b :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le

private theorem normalizedValuation_integer (a : (valuation K).valuationSubring) :
    normalizedValuation K (a : K) ≤ 1 := by
  rw [← (normalizedValuation K).map_one]
  exact (normalizedValuation_le_iff _ _).mpr (by
    rw [map_one]
    exact (Valuation.mem_valuationSubring_iff _ _).mp a.2)

private theorem normalizedValuation_uniformizer (π : (valuation K).valuationSubring)
    (hπ : (valuation K).IsUniformizer (π : K)) :
    normalizedValuation K (π : K) = exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hπlt : normalizedValuation K (π : K) < 1 := by
    change e (valuation K (π : K)) < 1
    simpa only [map_one] using e.strictMono hπ.val_lt_one
  obtain ⟨z, hz⟩ := valuation_surjective (e.symm (exp (-1 : ℤ)))
  have hz' : normalizedValuation K z = exp (-1 : ℤ) := by
    change e (valuation K z) = _
    rw [hz, e.apply_symm_apply]
  have hzlt : valuation K z < 1 := by
    have h : e (valuation K z) < e 1 := by
      change normalizedValuation K z < e 1
      rw [hz', map_one]
      simp
    exact e.toOrderIso.lt_iff_lt.mp h
  let a : (valuation K).valuationSubring := ⟨z, hzlt.le⟩
  have hamax : a ∈ maximalIdeal ((valuation K).valuationSubring) :=
    (Valuation.mem_maximalIdeal_iff (v := valuation K)).mpr hzlt
  obtain ⟨b, hb⟩ := (Ideal.mem_span_singleton.mp (hπ.is_generator ▸
    (show a ∈ maximalIdeal ((valuation K).valuationSubring) from hamax)) : π ∣ a)
  have hzb : z = (π : K) * (b : K) :=
    congrArg (fun x : (valuation K).valuationSubring => (x : K)) hb
  have hl : exp (-1 : ℤ) ≤ normalizedValuation K (π : K) := by
    rw [← hz', hzb, map_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (normalizedValuation_integer b)
      (zero_le : 0 ≤ normalizedValuation K (π : K))
  have hne : normalizedValuation K (π : K) ≠ 0 := (map_ne_zero _).mpr hπ.ne_zero
  have h₁ : (-1 : ℤ) ≤ log (normalizedValuation K (π : K)) :=
    (le_log_iff_exp_le hne).mpr hl
  have h₂ : log (normalizedValuation K (π : K)) < 0 :=
    (log_lt_iff_lt_exp hne).mpr (by simpa only [exp_zero] using hπlt)
  exact (exp_log hne).symm.trans (congrArg exp (by omega))

/-- The powers of the actual valuation-ring maximal ideal agree with the
normalized integer depth filtration. -/
theorem mem_idealPower_iff_normalizedValuation
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (n : ℕ) (z : (valuation K).valuationSubring) :
    z ∈ maximalIdeal ((valuation K).valuationSubring) ^ n ↔
      normalizedValuation K (z : K) ≤ exp (-(n : ℤ)) := by
  have hπpow : normalizedValuation K ((π : K) ^ n) = exp (-(n : ℤ)) := by
    rw [map_pow, normalizedValuation_uniformizer π hπ, ← exp_nsmul]
    congr 1
    simp
  rw [mem_maximalIdeal_pow_iff_factor π hπ.is_generator, ← hπpow]
  constructor
  · rintro ⟨b, hb⟩
    have he := congrArg (fun x : (valuation K).valuationSubring => (x : K)) hb
    change (z : K) = (π : K) ^ n * (b : K) at he
    rw [he, map_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (normalizedValuation_integer b)
      (zero_le : 0 ≤ normalizedValuation K ((π : K) ^ n))
  · intro hz
    have hne : (π : K) ^ n ≠ 0 := pow_ne_zero _ hπ.ne_zero
    have hb : valuation K ((z : K) / (π : K) ^ n) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hne))]
      exact (normalizedValuation_le_iff _ _).mp hz
    refine ⟨⟨(z : K) / (π : K) ^ n, hb⟩, Subtype.ext ?_⟩
    change (z : K) = (π : K) ^ n * ((z : K) / (π : K) ^ n)
    rw [mul_div_cancel₀ _ hne]

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra K E] [ValuativeExtension K E]

private theorem normalizedValuation_map (a : K) :
    normalizedValuation E (algebraMap K E a) =
      normalizedValueGroupMap K E (normalizedValuation K a) := by
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let eE := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  change eE (valuation E (algebraMap K E a)) =
    eE (ValuativeExtension.mapValueGroupWithZero K E (eK.symm (eK (valuation K a))))
  rw [eK.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]

/-- Computing one uniformizer value determines restriction of normalized
valuations on the whole coefficient field. -/
theorem normalizedValuation_extension_power (π : K) (hπ : normalizedValuation K π = exp (-1 : ℤ))
    (d : ℕ) (hd : 0 < d)
    (he : normalizedValuation E (algebraMap K E π) = exp (-(d : ℤ))) (a : K) :
    normalizedValuation E (algebraMap K E a) = normalizedValuation K a ^ d := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [zero_pow hd.ne']
  have ha' : normalizedValuation K a ≠ 0 := (map_ne_zero _).mpr ha
  let m := -log (normalizedValuation K a)
  have hpow : normalizedValuation K a = exp (-1 : ℤ) ^ m := by
    have hm : m • (-1 : ℤ) = log (normalizedValuation K a) := by
      simp [m]
    rw [← exp_zsmul, hm, exp_log ha']
  have hf := (normalizedValuation_map (E := E) π).symm.trans he
  rw [hπ] at hf
  rw [normalizedValuation_map, hpow, map_zpow₀, hf, ← exp_zsmul, ← exp_zsmul, ← exp_nsmul]
  congr 1
  simp only [zsmul_eq_mul, nsmul_eq_mul]
  ring

/-- An automorphism preserving the valuation ring and fixing the
uniformizer preserves all normalized depths. -/
theorem normalizedValuation_fixed_uniformizer
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (σ : K ≃+* K) (hfix : σ (π : K) = π)
    (e : (valuation K).valuationSubring ≃+* (valuation K).valuationSubring)
    (he : ∀ b, (e b : K) = σ (b : K)) (z : K) :
    normalizedValuation K (σ z) = normalizedValuation K z := by
  let v := normalizedValuation K
  have hO (x : K) : σ x ∈ (valuation K).valuationSubring ↔ x ∈ (valuation K).valuationSubring := by
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := e.surjective ⟨σ x, hx⟩
      have hh : σ (b : K) = σ x :=
        (he b).symm.trans (congrArg (fun z : (valuation K).valuationSubring => (z : K)) hb)
      exact ((σ.injective hh) ▸ b.2)
    · intro hx
      exact (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).2
  have hv (x : K) (m : ℤ) : v x ≤ exp m ↔ x / (π : K) ^ (-m) ∈ (valuation K).valuationSubring := by
    have hp : v ((π : K) ^ (-m)) = exp m := by
      rw [map_zpow₀, normalizedValuation_uniformizer π hπ, ← exp_zsmul]
      congr 1
      simp
    have hnn : 0 < v ((π : K) ^ (-m)) := by rw [hp]; exact exp_pos
    calc
      v x ≤ exp m ↔ v (x / (π : K) ^ (-m)) ≤ 1 := by rw [map_div₀, div_le_one₀ hnn, hp]
      _ ↔ x / (π : K) ^ (-m) ∈ (valuation K).valuationSubring := by
        rw [Valuation.mem_valuationSubring_iff, ← (valuation K).map_one,
          ← normalizedValuation_le_iff, map_one]
  have hbound (m : ℤ) : v (σ z) ≤ exp m ↔ v z ≤ exp m := by
    rw [hv, hv]
    simpa only [map_div₀, map_zpow₀, hfix] using hO (z / (π : K) ^ (-m))
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz₁ : v z ≠ 0 := (map_ne_zero _).mpr hz
  have hz₂ : v (σ z) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr hz)
  have hl := hbound (log (v z))
  have hr := hbound (log (v (σ z)))
  rw [exp_log hz₁] at hl
  rw [exp_log hz₂] at hr
  exact le_antisymm (hl.mpr le_rfl) (hr.mp le_rfl)

end NormalizedDepth

section PairedCoefficients

open ValuativeRel IsLocalRing

/-- Any integral automorphism fixing an integral subring with surjective
residue map acts trivially on the residue field. -/
theorem residue_fixed_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hf : Function.Surjective (ResidueField.map f)) (τ : B ≃+* B)
    (hτ : ∀ a, τ (f a) = f a) (b : B) :
    IsLocalRing.residue B (τ b) = IsLocalRing.residue B b := by
  letI := IsLocalHom.of_surjective τ.toRingHom τ.surjective
  obtain ⟨c, hc⟩ := hf (IsLocalRing.residue B b)
  obtain ⟨a, rfl⟩ := residue_surjective c
  change IsLocalRing.residue B (f a) = IsLocalRing.residue B b at hc
  have he := congrArg (ResidueField.map τ.toRingHom) hc
  change IsLocalRing.residue B (τ (f a)) = IsLocalRing.residue B (τ b) at he
  rw [hτ, hc] at he
  exact he.symm

theorem uniformizer_conjugate_unit {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B]
    (π : B) (hπ : maximalIdeal B = Ideal.span {π}) (τ : B ≃+* B) :
    ∃ ε : Bˣ, τ π = (ε : B) * π := by
  have hs : Ideal.span ({τ π} : Set B) = Ideal.span {π} := by
    calc
      Ideal.span {τ π} = (Ideal.span {π}).map τ.toRingHom := by
        rw [Ideal.map_span, Set.image_singleton]
        rfl
      _ = Ideal.span {π} := by
        rw [← hπ, IsLocalRing.map_maximalIdeal_of_surjective τ.toRingHom τ.surjective]
  obtain ⟨ε, hε⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.symm
  exact ⟨ε, by simpa only [mul_comm] using hε.symm⟩

attribute [local instance] ExceptionalLocalRootCoordinates.canonicalExtension

variable {K E : Type*} [Field K] [Field E] [ValuativeRel K] [ValuativeRel E]
  [Algebra K E] [ValuativeExtension K E]

/-- The two absolute slots of a paired parameter have a common scaled
uniformizer power. Their remaining residues differ by the two marking units
and by the residue of the conjugate-uniformizer unit raised to the parameter
depth. Substitution of the near-one torus differences gives the same formula. -/
theorem pairedParameterFactors (τ : K ≃+* K)
    (τ₀ : (valuation K).valuationSubring ≃+* (valuation K).valuationSubring)
    (hτ₀ : ∀ b, (τ₀ b : K) = τ (b : K))
    (hτκ : ∀ b, IsLocalRing.residue _ (τ₀ b) = IsLocalRing.residue _ b)
    (π : (valuation K).valuationSubring)
    (hπ : maximalIdeal ((valuation K).valuationSubring) = Ideal.span {π})
    (ξ : Eˣ) (d : ℕ) (hξ : (ξ : E) ^ d = algebraMap K E (π : K))
    (c₁ c₂ : ((valuation E).valuationSubring)ˣ) (s m : ℤ) (b : (valuation K).valuationSubring) :
    ∃ (ε : ((valuation K).valuationSubring)ˣ) (z₁ z₂ : (valuation E).valuationSubring),
      τ (π : K) = ((ε : (valuation K).valuationSubring) : K) * (π : K) ∧
      (ξ : E) ^ s * (c₁ : (valuation E).valuationSubring) * algebraMap K E ((π : K) ^ m * (b : K)) =
        (ξ : E) ^ (s + (d : ℤ) * m) * (z₁ : E) ∧
      (ξ : E) ^ s * (c₂ : (valuation E).valuationSubring) *
        algebraMap K E (τ ((π : K) ^ m * (b : K))) =
        (ξ : E) ^ (s + (d : ℤ) * m) * (z₂ : E) ∧
      let red := IsLocalRing.residue ((valuation E).valuationSubring)
      let f := algebraMap (valuation K).valuationSubring (valuation E).valuationSubring
      red z₁ = red c₁ * red (f b) ∧
      red z₂ = (red c₂ * red (f ((ε ^ m : ((valuation K).valuationSubring)ˣ) :
        (valuation K).valuationSubring))) * red (f b) := by
  obtain ⟨ε, he⟩ := uniformizer_conjugate_unit π hπ τ₀
  have hε : τ (π : K) = ((ε : (valuation K).valuationSubring) : K) * (π : K) :=
    (hτ₀ π).symm.trans (congrArg (fun z : (valuation K).valuationSubring => (z : K)) he)
  let f := algebraMap (valuation K).valuationSubring (valuation E).valuationSubring
  let z₁ := (c₁ : (valuation E).valuationSubring) * f b
  let z₂ := (c₂ : (valuation E).valuationSubring) *
    f ((ε ^ m : ((valuation K).valuationSubring)ˣ) : (valuation K).valuationSubring) * f (τ₀ b)
  have fcoe (z : (valuation K).valuationSubring) : (f z : E) = algebraMap K E (z : K) := rfl
  have hmul (z w : (valuation E).valuationSubring) :
      ((z * w : (valuation E).valuationSubring) : E) = (z : E) * (w : E) := rfl
  have hunit : (((ε ^ m : ((valuation K).valuationSubring)ˣ) :
      (valuation K).valuationSubring) : K) = (((ε : (valuation K).valuationSubring) : K) ^ m) := by
    let i := (valuation K).valuationSubring.subtype.toMonoidHom
    change ((Units.map i (ε ^ m) : Kˣ) : K) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hpow : (ξ : E) ^ (s + (d : ℤ) * m) = (ξ : E) ^ s * (algebraMap K E (π : K)) ^ m := by
    rw [zpow_add₀ (Units.ne_zero ξ), zpow_mul, zpow_natCast, hξ]
  refine ⟨ε, z₁, z₂, hε, ?_, ?_, ?_⟩
  · rw [hpow, map_mul, map_zpow₀]
    simp only [z₁, hmul, fcoe]
    ac_rfl
  · rw [hpow, map_mul τ, map_zpow₀, hε, mul_zpow, map_mul, map_mul, map_zpow₀, map_zpow₀]
    simp only [z₂, hmul, fcoe, hunit, hτ₀, map_zpow₀]
    ring
  · let red := IsLocalRing.residue ((valuation E).valuationSubring)
    have hb : red (f (τ₀ b)) = red (f b) := by
      simpa only [ResidueField.map_residue] using
        congrArg (ResidueField.map f) (hτκ b)
    change red z₁ = red c₁ * red (f b) ∧
      red z₂ = (red c₂ * red (f ((ε ^ m : ((valuation K).valuationSubring)ˣ) :
        (valuation K).valuationSubring))) * red (f b)
    exact ⟨map_mul red _ _, by simp only [z₂, map_mul, hb]⟩

end PairedCoefficients

section TorusBasis

open IntegralSemisimpleModel

universe u

/-- In the marked adjoint datum the simple roots are a character basis.
The numbering gives exactly the indicated six torus coordinates. -/
theorem adjointSimpleCharacterBasis (D : BasedRootDatum.{u})
    (b : Fin 6 ≃ D.base.support) (h : D.datum.rootSpan ℤ = ⊤) :
    ∃ B : Module.Basis (Fin 6) ℤ D.X, ∀ i, B i = D.datum.root (b i).val := by
  let e : D.datum.rootSpan ℤ ≃ₗ[ℤ] D.X :=
    (LinearEquiv.ofEq _ _ h).trans (Submodule.topEquiv : (⊤ : Submodule ℤ D.X) ≃ₗ[ℤ] D.X)
  refine ⟨(D.base.toWeightBasisInt.map e).reindex b.symm, fun i => ?_⟩
  simp [e]

/-- Choosing arbitrary units on a character basis determines a unique
point of the marked split torus. -/
theorem torusValues_of_basis {D : BasedRootDatum.{u}} {index : Type*}
    (b : Module.Basis index ℤ D.X) (R : IntegralAlgebra.{u}) (v : index → Rˣ) :
    ∃! t : TorusValues D R, ∀ i, t (Multiplicative.ofAdd (b i)) = v i := by
  let x : D.X →ₗ[ℤ] Additive Rˣ := b.constr ℤ (fun i => Additive.ofMul (v i))
  let t : TorusValues D R := x.toAddMonoidHom.toMultiplicativeLeft
  have h (i : index) : t (Multiplicative.ofAdd (b i)) = v i := by
    exact congrArg Additive.toMul (b.constr_basis ℤ (fun i => Additive.ofMul (v i)) i)
  refine ⟨t, h, fun s hs => ?_⟩
  apply AddMonoidHom.toMultiplicativeLeft.symm.injective
  let y : D.X →ₗ[ℤ] Additive Rˣ := (AddMonoidHom.toMultiplicativeLeft.symm s).toIntLinearMap
  have hy : y = x := b.ext fun i => by
    change Additive.ofMul (s (Multiplicative.ofAdd (b i))) = Additive.ofMul (t (Multiplicative.ofAdd (b i)))
    rw [hs, h]
  exact congrArg LinearMap.toAddMonoidHom hy

end TorusBasis

section ScaledFace

open _root_.LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceCongruence
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel ExceptionalIwahoriCongruence Opposite
open ExceptionalValuedTorusNormalizer (invariantApartment)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open ExceptionalAffineRootSystems (FoldedRootDirection IsLongF4Doubled foldedDepthDenominator)
open ValuativeRel WithZero

universe u

attribute [local instance] integerAlgebra

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} {T : DiagramCompositum F L k σ} {A : FoldedApartment (R.diagram σ)}
    {X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A}
    {J : Set (A.roots.SimpleWall A.basepoint)} {x : invariantApartment D (R.diagram σ)}

private theorem auxiliaryValuation (S : ScaledFace T X J x) (z : T.field) :
    normalizedValuation S.E (algebraMap T.field S.E z) =
      normalizedValuation T.field z ^ S.d := by
  apply normalizedValuation_extension_power (algebraMap L T.field (S.uniformizer : L))
    ((T.unramified _).trans S.uniformizer_value) S.d S.d_pos _ z
  rw [← S.xi_power, map_pow, normalizedValuation_uniformizer S.xi S.xi_uniformizer,
    ← exp_nsmul]
  congr 1
  simp

private theorem rootScalingExponent (S : ScaledFace T X J x) (i : D.I) :
    ((D.datum.toLinearMap (D.datum.root i) S.cocharacter : ℤ) : ℚ) =
      (rootStep S (A.direction i) : ℚ) * A.roots.root (A.direction i) x := by
  let f := (ApartmentRoots.split D.datum ℚ).root i
  have h := congrArg f S.cocharacter_eq
  change RootData.extendFunctional ℚ (D.datum.root' i) (1 ⊗ₜ[ℤ] S.cocharacter) =
    f ((2 * (S.d : ℚ)) • x.val) at h
  rw [RootData.extendFunctional_one_tmul, map_smul, smul_eq_mul] at h
  have h' : ((D.datum.toLinearMap (D.datum.root i) S.cocharacter : ℤ) : ℚ) =
      (2 * (S.d : ℚ)) * f x.val := h
  rw [h', A.root_value]
  change (2 * (S.d : ℚ)) * f x.val =
    (rootStep S (A.direction i) : ℚ) * ((foldedDepthDenominator (A.direction i) : ℚ) * f x.val)
  by_cases hl : IsLongF4Doubled (A.direction i).val
  all_goals
    simp only [rootStep, foldedDepthDenominator, hl, ite_true, ite_false, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Nat.cast_one, Nat.cast_ofNat]
    ring

private theorem rootStep_pos (S : ScaledFace T X J x) (a : FoldedRootDirection) :
    0 < rootStep S a := by
  have hd : 0 < (S.d : ℤ) := by exact_mod_cast S.d_pos
  unfold rootStep
  split <;> positivity

private theorem normalizedUnitValue {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (u : ((valuation E).valuationSubring)ˣ) :
    normalizedValuation E ((u : (valuation E).valuationSubring) : E) = 1 := by
  let v := normalizedValuation E
  have hu := normalizedValuation_integer (u : (valuation E).valuationSubring)
  have hvinv := normalizedValuation_integer (K := E)
    ((u⁻¹ : ((valuation E).valuationSubring)ˣ) : (valuation E).valuationSubring)
  refine le_antisymm hu ?_
  have h : v ((u : (valuation E).valuationSubring) : E) *
      v ((u⁻¹ : ((valuation E).valuationSubring)ˣ) : (valuation E).valuationSubring) = 1 := by
    rw [← map_mul]
    have h := congrArg (fun a : (valuation E).valuationSubring => (a : E)) (Units.mul_inv u)
    rw [show ((u : (valuation E).valuationSubring) : E) *
      (((u⁻¹ : ((valuation E).valuationSubring)ˣ) : (valuation E).valuationSubring) : E) = 1 from h,
      map_one]
  change 1 ≤ v ((u : (valuation E).valuationSubring) : E)
  rw [← h]
  simpa using mul_le_mul_of_nonneg_left hvinv
    (zero_le : 0 ≤ v ((u : (valuation E).valuationSubring) : E))

private theorem normalizedIntegerUnitValue {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] (c : Integers.{u}ˣ) :
    letI := integerAlgebra E
    normalizedValuation E (algebraMap Integers.{u} E (c : Integers.{u})) = 1 := by
  let i : Integers.{u} →+* (valuation E).valuationSubring :=
    (Int.castRingHom _).comp ULift.ringEquiv.toRingHom
  change normalizedValuation E ((c : Integers.{u}).down : E) = 1
  have h := normalizedUnitValue (E := E) (Units.map i.toMonoidHom c)
  change normalizedValuation E (((c : Integers.{u}).down : (valuation E).valuationSubring) : E) = 1 at h
  exact h

private theorem rootRepresentative (a : FoldedRootDirection) :
    ∃ (i : D.I) (f : X.comparison.chart.parameter a →+* T.field),
      X.comparison.chart.UsesSlot i a f ∧
      ∀ z, normalizedValuation T.field (f z) =
        X.comparison.chart.value a z ^ (if IsLongF4Doubled a.val then (2 : ℕ) else 1) := by
  by_cases ha : IsLongF4Doubled a.val
  · obtain ⟨i, hi⟩ := A.surjective a
    have h := (A.long i).mp (hi.symm ▸ ha)
    obtain ⟨e, he, hv⟩ := X.singleton i h
    subst a
    refine ⟨i, (algebraMap k T.field).comp e.toRingHom, he, fun z => ?_⟩
    simp only [ha, ↓reduceIte, RingHom.comp_apply, X.ramification, hv]
    rfl
  · obtain ⟨i, hi, e, he, _, hv⟩ := X.pair a ha
    exact ⟨i, e.toRingHom, he, fun z => by simpa [ha] using (hv z).symm⟩

private theorem intUnit_ne_zero (c : Integers.{u}ˣ) :
    algebraMap Integers.{u} T.field (c : Integers.{u}) ≠ 0 :=
  Units.ne_zero (Units.map (algebraMap Integers.{u} T.field).toMonoidHom c)

private theorem chartParameters_injective (T : DiagramCompositum F L k σ)
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (z w : X.comparison.chart.chart.torus × (∀ a, X.comparison.chart.parameter a))
    (he : X.comparison.chart.chart.coordinates z.1 z.2 =
      X.comparison.chart.chart.coordinates w.1 w.2) : z = w := by
  let C := X.comparison.chart
  refine Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) he)) ?_
  funext a
  obtain ⟨i, hi⟩ := A.surjective a
  by_cases hp : D.base.IsPos i
  · obtain ⟨s, hs⟩ := List.mem_iff_get.mp ((C.positive_enumerates.2 i).mpr hp)
    have hs' : C.positive[s] = i := hs
    have hslot : C.chart.pos s = a :=
      (C.pos_slots s).trans ((congrFun X.directions _).trans ((congrArg A.direction hs').trans hi))
    have h : z.2 (C.chart.pos s) = w.2 (C.chart.pos s) :=
      (C.chart.posMap s).injective (mul_left_cancel₀ (intUnit_ne_zero (T := T) (C.chart.posUnit s))
        (congrArg (fun z => z.2.2 s) he))
    exact hslot ▸ h
  · obtain ⟨s, hs⟩ := List.mem_iff_get.mp ((C.negative_enumerates.2 i).mpr hp)
    have hs' : C.negative[s] = i := hs
    have hslot : C.chart.neg s = a :=
      (C.neg_slots s).trans ((congrFun X.directions _).trans ((congrArg A.direction hs').trans hi))
    have h : z.2 (C.chart.neg s) = w.2 (C.chart.neg s) :=
      (C.chart.negMap s).injective (mul_left_cancel₀ (intUnit_ne_zero (T := T) (C.chart.negUnit s))
        (congrArg (fun z => z.1 s) he))
    exact hslot ▸ h

private theorem rootDepthBound (S : ScaledFace T X J x) (Y : Building X.comparison)
    (t : Weights (A.roots.SimpleWall A.basepoint))
    (hx : rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t)
    {n : ℕ} (hn : 0 < n) (i : D.I) (a : FoldedRootDirection) (hia : A.direction i = a)
    (r : ℤᵐ⁰) (c : Integers.{u}ˣ) (z : T.field)
    (hz : normalizedValuation T.field z = r ^ (if IsLongF4Doubled a.val then (2 : ℕ) else 1))
    (w : (valuation S.E).valuationSubring)
    (hw : w ∈ IsLocalRing.maximalIdeal ((valuation S.E).valuationSubring) ^ n)
    (he : (w : S.E) = (S.xi : S.E) ^ D.datum.toLinearMap (D.datum.root i) S.cocharacter *
      algebraMap T.field S.E (algebraMap Integers.{u} T.field (c : Integers.{u}) * z)) :
    r ≤ exp (-threshold (A.roots.root a A.basepoint)) := by
  let s := D.datum.toLinearMap (D.datum.root i) S.cocharacter
  have hs := rootScalingExponent S i
  rw [hia] at hs
  apply scaledDepthOfParameterAtAlcove Y t x hx a s (rootStep S a)
    (rootStep_pos S a) hs r
  have h := (mem_idealPower_iff_normalizedValuation S.xi S.xi_uniformizer n w).mp hw
  have hn' : exp (-(n : ℤ)) < (1 : ℤᵐ⁰) := by
    rw [exp_lt_one_iff]
    omega
  apply lt_of_le_of_lt _ hn'
  have hval : normalizedValuation S.E (w : S.E) =
      exp (-s) * r ^ rootStep S a := by
    rw [he, map_mul, map_zpow₀, normalizedValuation_uniformizer S.xi S.xi_uniformizer,
      auxiliaryValuation S, map_mul, normalizedIntegerUnitValue, one_mul, hz, ← pow_mul]
    have hs' : (exp (-1 : ℤ) : ℤᵐ⁰) ^ s = exp (-s) := by
      rw [← exp_zsmul]
      congr 1
      simp
    rw [hs']
    unfold rootStep
    by_cases ha : IsLongF4Doubled a.val
    all_goals simp [ha, mul_comm, ← zpow_natCast]
  rwa [← hval]

/-- At a point of the actual parahoric, every positive congruence depth is
tested by its original marked field chart and its scaled integral chart. -/
theorem parahoricPointCongruence (S : ScaledFace T X J x)
    {n : ℕ} (hn : 0 < n) (g : parahoric X.comparison J) :
    g ∈ congruenceSubgroup S n ↔
      ∃! z : CellValues D (integralRing T.field) X.comparison.chart.negative
          X.comparison.chart.positive,
        cellValue M.toIntegralMarking (integralRing T.field) X.comparison.chart.negative
          X.comparison.chart.positive z = X.points g ∧
        ∃ w, ScaledCoordinates S z w ∧ CellDepth S n w := by
  let f := integralRingMap (algebraMap T.field S.E)
  have hf : Function.Surjective (integralSpec.map f.op).left := by
    change Function.Surjective (Spec.map (CommRingCat.ofHom (algebraMap T.field S.E)))
    intro z
    exact ⟨default, Subsingleton.elim _ _⟩
  let i := localIntegersInclusion S.E
  have hi : Function.Injective i.hom := Subtype.val_injective
  let C := X.comparison.chart
  exact scaledIdentityCongruence M.toIntegralMarking f hf i hi C.negative C.positive
    C.negative_enumerates C.positive_enumerates
    (cocharacter D S.cocharacter (integralRing S.E)
      (Units.mk0 (S.xi : S.E) S.xi_uniformizer.ne_zero))
    (X.points g) (S.point g) (S.point_eq g) hn

set_option maxHeartbeats 600000 in
/-- Positive scaled coordinates of an actual rational point put it in the
marked Iwahori of the standard alcove. -/
theorem scaledCoordinatesInIwahori (S : ScaledFace T X J x) (Y : Building X.comparison)
    (t : Weights (A.roots.SimpleWall A.basepoint))
    (hx : rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t)
    {n : ℕ} (hn : 0 < n) (g : GroupPoints R.descent.group.val (CommAlgCat.of F k))
    (z : CellValues D (integralRing T.field) X.comparison.chart.negative X.comparison.chart.positive)
    (w : CellValues D (localIntegers S.E) X.comparison.chart.negative X.comparison.chart.positive)
    (hz : cellValue M.toIntegralMarking (integralRing T.field) X.comparison.chart.negative
      X.comparison.chart.positive z = X.points g)
    (he : ScaledCoordinates S z w) (hw : CellDepth S n w) : g ∈ X.comparison.I := by
  let C := X.comparison.chart
  have hmem : cellValue M.toIntegralMarking (integralRing T.field) C.negative C.positive z ∈
      X.points.range := ⟨g, hz.symm⟩
  obtain ⟨tor, roots, rfl⟩ := (C.rational z).mp hmem
  have htor (χ : Multiplicative D.X) :
      normalizedValuation T.field (tor.val χ : T.field) = 1 := by
    have hb := congrArg (fun z => (z.2.1 χ : integralRing S.E)) he
    change ((w.2.1 χ : (valuation S.E).valuationSubring) : S.E) =
      algebraMap T.field S.E (tor.val χ : T.field) at hb
    have h := normalizedUnitValue (w.2.1 χ)
    rw [hb, auxiliaryValuation S] at h
    exact (pow_eq_one_iff_of_nonneg zero_le S.d_pos.ne').mp h
  have hlayers (a : FoldedRootDirection) :
      C.value a (roots a) ≤ exp (-threshold (A.roots.root a A.basepoint)) := by
    obtain ⟨i, f, hf, hv⟩ := rootRepresentative (X := X) a
    have hi : A.direction i = a := (congrFun X.directions i).symm.trans hf.1
    have transport (b c : FoldedRootDirection) (h : b = c) :
        (h ▸ roots b : C.parameter c) = roots c := by subst c; rfl
    by_cases hp : D.base.IsPos i
    · obtain ⟨s, hs⟩ := List.mem_iff_get.mp ((C.positive_enumerates.2 i).mpr hp)
      have hs' : C.positive[s] = i := hs
      have hsa : C.chart.pos s = a := (C.pos_slots s).trans
        ((congrFun X.directions _).trans ((congrArg A.direction hs').trans hi))
      have hr := hf.2.2 s hsa (roots a) hs'
      rw [transport] at hr
      have h := congrArg (fun z => z.2.2 s) he
      change (w.2.2 s : S.E) =
        (↑((Units.mk0 (S.xi : S.E) S.xi_uniformizer.ne_zero) ^
          D.datum.toLinearMap (D.datum.root C.positive[s]) S.cocharacter) : S.E) *
        algebraMap T.field S.E (algebraMap Integers.{u} T.field
          (C.chart.posUnit s : Integers.{u}) * C.chart.posMap s (roots (C.chart.pos s))) at h
      rw [Units.val_zpow_eq_zpow_val, hs', hr] at h
      exact rootDepthBound S Y t hx hn i a hi _ _ _ (hv _) _ (hw.2.2 s) h
    · obtain ⟨s, hs⟩ := List.mem_iff_get.mp ((C.negative_enumerates.2 i).mpr hp)
      have hs' : C.negative[s] = i := hs
      have hsa : C.chart.neg s = a := (C.neg_slots s).trans
        ((congrFun X.directions _).trans ((congrArg A.direction hs').trans hi))
      have hr := hf.2.1 s hsa (roots a) hs'
      rw [transport] at hr
      have h := congrArg (fun z => z.1 s) he
      change (w.1 s : S.E) =
        (↑((Units.mk0 (S.xi : S.E) S.xi_uniformizer.ne_zero) ^
          D.datum.toLinearMap (D.datum.root C.negative[s]) S.cocharacter) : S.E) *
        algebraMap T.field S.E (algebraMap Integers.{u} T.field
          (C.chart.negUnit s : Integers.{u}) * C.chart.negMap s (roots (C.chart.neg s))) at h
      rw [Units.val_zpow_eq_zpow_val, hs', hr] at h
      exact rootDepthBound S Y t hx hn i a hi _ _ _ (hv _) _ (hw.1 s) h
  apply (X.bruhat.base_chart g).mpr
  refine ⟨(tor, roots), ⟨hz, htor, hlayers⟩, fun q hq => ?_⟩
  apply chartParameters_injective T X
  exact (markedCellChart M.toIntegralMarking _ _ C.negative_enumerates C.positive_enumerates).1 _
    (hq.1.trans hz.symm)

/-- For an actual rational point, the scaled chart depth conditions are
equivalent to both belonging to the parahoric and reducing to identity at
the indicated precision. -/
theorem parahoricChartCongruence (S : ScaledFace T X J x) (Y : Building X.comparison)
    (t : Weights (A.roots.SimpleWall A.basepoint))
    (hx : rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t)
    {n : ℕ} (hn : 0 < n) (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    (∃ hp : g ∈ parahoric X.comparison J,
      (⟨g, hp⟩ : parahoric X.comparison J) ∈ congruenceSubgroup S n) ↔
        ∃! z : CellValues D (integralRing T.field) X.comparison.chart.negative
            X.comparison.chart.positive,
          cellValue M.toIntegralMarking (integralRing T.field) X.comparison.chart.negative
            X.comparison.chart.positive z = X.points g ∧
          ∃ w, ScaledCoordinates S z w ∧ CellDepth S n w := by
  constructor
  · rintro ⟨hp, h⟩
    exact (parahoricPointCongruence S hn ⟨g, hp⟩).mp h
  · intro h
    have hall := h
    obtain ⟨z, ⟨hz, w, hzw, hw⟩, _⟩ := h
    have hi := scaledCoordinatesInIwahori S Y t hx hn g z w hz hzw hw
    have hp : g ∈ parahoric X.comparison J := Subgroup.subset_closure (Or.inl hi)
    exact ⟨hp, (parahoricPointCongruence S hn ⟨g, hp⟩).mpr hall⟩

theorem congruenceSubgroup_antitone (S : ScaledFace T X J x) :
    Antitone (congruenceSubgroup S) := by
  intro n m hnm g hg
  let O := localIntegers S.E
  let I := IsLocalRing.maximalIdeal O
  let f : congruenceRing O m ⟶ congruenceRing O n :=
    CommAlgCat.ofHom (Ideal.Quotient.factorₐ Integers.{u}
      (Ideal.pow_le_pow_right hnm : I ^ m ≤ I ^ n))
  have hf : congruenceHom O m ≫ f = congruenceHom O n := rfl
  change changeRingHom M.group (congruenceHom O m) (S.point g) = 1 at hg
  change changeRingHom M.group (congruenceHom O n) (S.point g) = 1
  rw [← hf]
  change ((integralPointFunctor M.group).map (congruenceHom O m ≫ f)).hom (S.point g) = 1
  rw [Functor.map_comp]
  change changeRingHom M.group f
    (changeRingHom M.group (congruenceHom O m) (S.point g)) = 1
  rw [hg, map_one]

private theorem scaledPoint_injective (S : ScaledFace T X J x) :
    Function.Injective S.point := by
  intro g h he
  have hg := S.point_eq g
  have hh := S.point_eq h
  rw [he, hh] at hg
  have hgh := (MulAut.conj _).injective hg
  have H := (changeRing_injective M.toIntegralMarking
    (integralRingMap (algebraMap T.field S.E)) (algebraMap T.field S.E).injective) hgh
  exact Subtype.ext (X.comparison.point_injective H.symm)

theorem congruenceSubgroup_separated (S : ScaledFace T X J x)
    (g : parahoric X.comparison J) (hg : ∀ n, 0 < n → g ∈ congruenceSubgroup S n) :
    g = 1 := by
  let O := localIntegers S.E
  let I := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O := inferInstanceAs
    (IsDiscreteValuationRing (Valuation.integer (ValuativeRel.valuation S.E)))
  have vanish (z : O) (hz : ∀ n : ℕ, 0 < n → z ∈ I ^ n) : z = 0 := by
    have hz' : z ∈ ⨅ n : ℕ, I ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n => exact hz _ n.succ_pos
    rw [Ideal.iInf_pow_eq_bot_of_isDomain I (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at hz'
    exact hz'
  let C := X.comparison.chart
  have each (n : ℕ) (hn : 0 < n) := markedIdentityCongruence M.toIntegralMarking O
    C.negative C.positive C.negative_enumerates C.positive_enumerates hn (S.point g)
  obtain ⟨z, hz, _⟩ := (each 1 Nat.one_pos).mp (hg 1 Nat.one_pos)
  have hzb (n : ℕ) (hn : 0 < n) :
      (∀ i, z.1 i ∈ I ^ n) ∧ (∀ χ, (z.2.1 χ : O) - 1 ∈ I ^ n) ∧
        (∀ i, z.2.2 i ∈ I ^ n) := by
    obtain ⟨w, hw, _⟩ := (each n hn).mp (hg n hn)
    have he := (markedCellChart M.toIntegralMarking C.negative C.positive
      C.negative_enumerates C.positive_enumerates).1 O (hw.1.trans hz.1.symm)
    rw [he] at hw
    exact hw.2
  have hz0 : z = (0, 1, 0) := by
    apply Prod.ext
    · exact funext fun i => vanish _ fun n hn => (hzb n hn).1 i
    · apply Prod.ext
      · exact MonoidHom.ext fun χ => Units.ext <| sub_eq_zero.mp <|
          vanish _ fun n hn => (hzb n hn).2.1 χ
      · exact funext fun i => vanish _ fun n hn => (hzb n hn).2.2 i
  apply scaledPoint_injective S
  rw [map_one, ← hz.1, hz0, cellValue_one]

private theorem congruenceCoordinates_exist (S : ScaledFace T X J x)
    {n : ℕ} (hn : 0 < n) (g : congruenceSubgroup S n) :
    ∃ w : CellValues D (localIntegers S.E) X.comparison.chart.negative X.comparison.chart.positive,
      cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive w =
        S.point (g : parahoric X.comparison J) ∧ CellDepth S n w := by
  have h := markedIdentityCongruence M.toIntegralMarking (localIntegers S.E) _ _
    X.comparison.chart.negative_enumerates X.comparison.chart.positive_enumerates
    hn (S.point (g : parahoric X.comparison J))
  exact (h.mp g.2).exists

/-- The absolute chart of a point in a positive congruence subgroup. -/
def congruenceCoordinates (S : ScaledFace T X J x)
    {n : ℕ} (hn : 0 < n) (g : congruenceSubgroup S n) :
    CellValues D (localIntegers S.E) X.comparison.chart.negative X.comparison.chart.positive :=
  (congruenceCoordinates_exist S hn g).choose

theorem congruenceCoordinates_spec (S : ScaledFace T X J x)
    {n : ℕ} (hn : 0 < n) (g : congruenceSubgroup S n) :
    cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive
        (congruenceCoordinates S hn g) = S.point (g : parahoric X.comparison J) ∧
      CellDepth S n (congruenceCoordinates S hn g) :=
  (congruenceCoordinates_exist S hn g).choose_spec

private theorem cellDepth_iff_truncatedIdentity (S : ScaledFace T X J x)
    (n : ℕ) (w : CellValues D (localIntegers S.E) X.comparison.chart.negative
      X.comparison.chart.positive) :
    CellDepth S n w ↔ mapCellValues (congruenceHom (localIntegers S.E) n) w = (0, 1, 0) := by
  let f := congruenceHom (localIntegers S.E) n
  constructor
  · rintro ⟨hn, ht, hp⟩
    exact Prod.ext (funext (fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (hn i))) <|
      Prod.ext (MonoidHom.ext fun χ => Units.ext (Ideal.Quotient.eq.mpr (ht χ)))
        (funext fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (hp i))
  · intro h
    refine ⟨fun i => Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrArg Prod.fst h) i), ?_,
      fun i => Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrArg (fun z => z.2.2) h) i)⟩
    intro χ
    apply Ideal.Quotient.eq.mp
    change f.hom (w.2.1 χ : localIntegers S.E) = f.hom 1
    rw [map_one]
    exact congrArg (fun z : CellValues D (congruenceRing (localIntegers S.E) n)
      X.comparison.chart.negative X.comparison.chart.positive =>
        (z.2.1 χ : congruenceRing (localIntegers S.E) n)) h

private theorem congruenceCoordinates_prod (S : ScaledFace T X J x)
    {n : ℕ} (hn : 0 < n) (g h : congruenceSubgroup S n) :
    let z := congruenceCoordinates S hn g
    let w := congruenceCoordinates S hn h
    let f := congruenceHom (localIntegers S.E) (n + 1)
    mapCellValues f (congruenceCoordinates S hn (g * h)) =
      mapCellValues f (z.1 + w.1, z.2.1 * w.2.1, z.2.2 + w.2.2) := by
  intro z w f
  let C := X.comparison.chart
  let V := markedCellChart M.toIntegralMarking _ _ C.negative_enumerates C.positive_enumerates
  have hz : cellValue M.toIntegralMarking _ C.negative C.positive z = S.point (g : _) :=
    (congruenceCoordinates_spec S hn g).1
  have hw : cellValue M.toIntegralMarking _ C.negative C.positive w = S.point (h : _) :=
    (congruenceCoordinates_spec S hn h).1
  have hp : cellValue M.toIntegralMarking _ C.negative C.positive
      (congruenceCoordinates S hn (g * h)) = S.point (g : _) * S.point (h : _) :=
    (congruenceCoordinates_spec S hn (g * h)).1.trans (S.point.map_mul _ _)
  have he := congruenceCellValue_mul M.toIntegralMarking (localIntegers S.E) hn
    C.negative C.positive z w
      ((cellDepth_iff_truncatedIdentity S n z).mp (congruenceCoordinates_spec S hn g).2)
      ((cellDepth_iff_truncatedIdentity S n w).mp (congruenceCoordinates_spec S hn h).2)
      C.negative_enumerates C.positive_enumerates
  apply V.1 _
  rw [← V.2, ← V.2]
  rw [hz, hw] at he
  change changeRingHom M.group f _ = changeRingHom M.group f _
  rwa [hp]

theorem congruenceSubgroup_stable (S : ScaledFace T X J x)
    {n : ℕ} (hn : 0 < n) (σ' : Gal(k/F)) (g : congruenceSubgroup S n) :
    S.action σ' g ∈ congruenceSubgroup S n := by
  let w := congruenceCoordinates S hn g
  have ⟨hw, hb⟩ := congruenceCoordinates_spec S hn g
  let e := S.integralCoefficient σ'
  let f : localIntegers S.E ⟶ localIntegers S.E := integralRingMap e.toRingHom
  let C := X.comparison.chart
  have h := ((markedCellChart M.toIntegralMarking _ _ C.negative_enumerates C.positive_enumerates).2
    f w).symm.trans ((congrArg (changeRingHom M.group f) hw).trans (S.point_equivariant σ' g).symm)
  have hm (b : (valuation S.E).valuationSubring)
      (hb : b ∈ IsLocalRing.maximalIdeal ((valuation S.E).valuationSubring) ^ n) :
      e b ∈ IsLocalRing.maximalIdeal ((valuation S.E).valuationSubring) ^ n := by
    have he := Ideal.mem_map_of_mem e.toRingHom hb
    rwa [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective] at he
  apply (markedIdentityCongruence M.toIntegralMarking _ _ _
    C.negative_enumerates C.positive_enumerates hn _).mpr
  refine ⟨mapCellValues f w, ⟨h, (fun i => hm _ (hb.1 i)), ?_,
    (fun i => hm _ (hb.2.2 i))⟩, ?_⟩
  · intro χ
    change e (w.2.1 χ : (valuation S.E).valuationSubring) - 1 ∈
      IsLocalRing.maximalIdeal ((valuation S.E).valuationSubring) ^ n
    simpa only [map_sub, map_one] using hm _ (hb.2.1 χ)
  · intro a ha
    exact (markedCellChart M.toIntegralMarking _ _ C.negative_enumerates
      C.positive_enumerates).1 _ (ha.1.trans h.symm)

open IsLocalRing

/-- The ambient space of absolute leading entries of the scaled chart. -/
abbrev AbsoluteLeadingVectors (S : ScaledFace T X J x) :=
  (Fin X.comparison.chart.negative.length → ExceptionalAffineBruhat.residue S.E) ×
    (Multiplicative D.X → ExceptionalAffineBruhat.residue S.E) ×
    (Fin X.comparison.chart.positive.length → ExceptionalAffineBruhat.residue S.E)

private def leadingEntries (S : ScaledFace T X J x) (n : ℕ)
    (w : CellValues D (localIntegers S.E) X.comparison.chart.negative
      X.comparison.chart.positive) (hw : CellDepth S n w) : AbsoluteLeadingVectors S :=
  let f := leadingCoefficient S.xi S.xi_uniformizer.is_generator n
  (fun i => f ⟨w.1 i, hw.1 i⟩, fun χ => f ⟨(w.2.1 χ : localIntegers S.E) - 1, hw.2.1 χ⟩,
    fun i => f ⟨w.2.2 i, hw.2.2 i⟩)

private theorem leadingEntries_congruent (S : ScaledFace T X J x) (n : ℕ)
    (z w : CellValues D (localIntegers S.E) X.comparison.chart.negative
      X.comparison.chart.positive) (hz : CellDepth S n z) (hw : CellDepth S n w)
    (heq : mapCellValues (congruenceHom (localIntegers S.E) (n + 1)) z =
      mapCellValues (congruenceHom (localIntegers S.E) (n + 1)) w) :
    leadingEntries S n z hz = leadingEntries S n w hw := by
  let C := X.comparison.chart
  let hπ := S.xi_uniformizer.is_generator
  have hne : S.xi ≠ 0 := fun h => S.xi_uniformizer.ne_zero (congrArg Subtype.val h)
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun χ => ?_) (funext fun i => ?_))
  · exact (leadingCoefficient_eq_iff S.xi hπ _ _ hne).mpr
      (Ideal.Quotient.eq.mp (congrFun (congrArg Prod.fst heq) i))
  · apply (leadingCoefficient_eq_iff S.xi hπ _ _ hne).mpr
    change (z.2.1 χ : localIntegers S.E) - 1 - ((w.2.1 χ : localIntegers S.E) - 1) ∈ _
    rw [sub_sub_sub_cancel_right]
    exact Ideal.Quotient.eq.mp (congrArg
      (fun v : CellValues D (congruenceRing (localIntegers S.E) (n + 1)) C.negative C.positive =>
        (v.2.1 χ : congruenceRing (localIntegers S.E) (n + 1))) heq)
  · exact (leadingCoefficient_eq_iff S.xi hπ _ _ hne).mpr
      (Ideal.Quotient.eq.mp (congrFun (congrArg (fun v => v.2.2) heq) i))

private theorem cellDepth_mul (S : ScaledFace T X J x) (n : ℕ)
    (z w : CellValues D (localIntegers S.E) X.comparison.chart.negative X.comparison.chart.positive)
    (hz : CellDepth S n z) (hw : CellDepth S n w) :
    CellDepth S n (z.1 + w.1, z.2.1 * w.2.1, z.2.2 + w.2.2) := by
  let I := maximalIdeal (localIntegers S.E) ^ n
  refine ⟨fun i => I.add_mem (hz.1 i) (hw.1 i), fun χ => ?_,
    fun i => I.add_mem (hz.2.2 i) (hw.2.2 i)⟩
  change (z.2.1 χ : localIntegers S.E) * (w.2.1 χ : localIntegers S.E) - 1 ∈ I
  rw [show (z.2.1 χ : localIntegers S.E) * (w.2.1 χ : localIntegers S.E) - 1 =
    (z.2.1 χ : localIntegers S.E) * ((w.2.1 χ : localIntegers S.E) - 1) +
      ((z.2.1 χ : localIntegers S.E) - 1) by ring]
  exact I.add_mem (I.mul_mem_left _ (hw.2.1 χ)) (hz.2.1 χ)

/-- The absolute leading entries form an additive homomorphism on the
actual congruence subgroup. -/
def absoluteLeadingHom (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n) :
    congruenceSubgroup S n →* Multiplicative (AbsoluteLeadingVectors S) := by
  let V := AbsoluteLeadingVectors S
  let r (g : congruenceSubgroup S n) : Multiplicative V := Multiplicative.ofAdd
    (leadingEntries S n (congruenceCoordinates S hn g) (congruenceCoordinates_spec S hn g).2)
  have hne : S.xi ≠ 0 := fun h => S.xi_uniformizer.ne_zero (congrArg Subtype.val h)
  have hm (g h : congruenceSubgroup S n) : r (g * h) = r g * r h := by
    let z := congruenceCoordinates S hn g
    let w := congruenceCoordinates S hn h
    let hz := (congruenceCoordinates_spec S hn g).2
    let hw := (congruenceCoordinates_spec S hn h).2
    let p : CellValues D (localIntegers S.E) X.comparison.chart.negative X.comparison.chart.positive :=
      (z.1 + w.1, z.2.1 * w.2.1, z.2.2 + w.2.2)
    let hp : CellDepth S n p := cellDepth_mul S n z w hz hw
    let hprod := (congruenceCoordinates_spec S hn (g * h)).2
    change leadingEntries S n (congruenceCoordinates S hn (g * h)) hprod =
      leadingEntries S n z hz + leadingEntries S n w hw
    rw [leadingEntries_congruent S n _ p hprod hp (congruenceCoordinates_prod S hn g h)]
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun χ => ?_) (funext fun i => ?_))
    · exact leadingCoefficient_add S.xi S.xi_uniformizer.is_generator
        ⟨z.1 i, hz.1 i⟩ ⟨w.1 i, hw.1 i⟩ hne
    · exact leadingCoefficient_unit_mul S.xi S.xi_uniformizer.is_generator hn hne
        (z.2.1 χ) (w.2.1 χ) (hz.2.1 χ) (hw.2.1 χ) (hp.2.1 χ)
    · exact leadingCoefficient_add S.xi S.xi_uniformizer.is_generator
        ⟨z.2.2 i, hz.2.2 i⟩ ⟨w.2.2 i, hw.2.2 i⟩ hne
  refine { toFun := r, map_one' := ?_, map_mul' := hm }
  have h := hm 1 1
  rw [one_mul] at h
  exact mul_right_cancel (h.symm.trans (one_mul _).symm)

theorem absoluteLeadingHom_ker (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n)
    (g : congruenceSubgroup S n) :
    absoluteLeadingHom S hn g = 1 ↔ (g : parahoric X.comparison J) ∈ congruenceSubgroup S (n + 1) := by
  let w := congruenceCoordinates S hn g
  let hw := (congruenceCoordinates_spec S hn g).2
  let C := X.comparison.chart
  let O := localIntegers S.E
  let hπ := S.xi_uniformizer.is_generator
  have hne : S.xi ≠ 0 := fun h => S.xi_uniformizer.ne_zero (congrArg Subtype.val h)
  have hchart := markedCellChart M.toIntegralMarking _ _ C.negative_enumerates C.positive_enumerates
  change leadingEntries S n w hw = 0 ↔ changeRingHom M.group (congruenceHom O (n + 1))
    (S.point (g : _)) = 1
  rw [← (congruenceCoordinates_spec S hn g).1]
  change leadingEntries S n w hw = 0 ↔ changeRing (congruenceHom O (n + 1))
    (cellValue M.toIntegralMarking O C.negative C.positive w) = 1
  rw [hchart.2, ← cellValue_one M.toIntegralMarking _ C.negative C.positive,
    (hchart.1 _).eq_iff, ← cellDepth_iff_truncatedIdentity]
  constructor
  · intro h
    refine ⟨fun i => (leadingCoefficient_zero_iff S.xi hπ ⟨w.1 i, hw.1 i⟩ hne).mp ?_,
      fun χ => (leadingCoefficient_zero_iff S.xi hπ ⟨(w.2.1 χ : O) - 1, hw.2.1 χ⟩ hne).mp ?_,
      fun i => (leadingCoefficient_zero_iff S.xi hπ ⟨w.2.2 i, hw.2.2 i⟩ hne).mp ?_⟩
    · exact congrFun (congrArg Prod.fst h) i
    · exact congrFun (congrArg (fun z => z.2.1) h) χ
    · exact congrFun (congrArg (fun z => z.2.2) h) i
  · intro h
    exact Prod.ext (funext fun i => (leadingCoefficient_zero_iff S.xi hπ _ hne).mpr (h.1 i)) <|
      Prod.ext (funext fun χ => (leadingCoefficient_zero_iff S.xi hπ _ hne).mpr (h.2.1 χ))
        (funext fun i => (leadingCoefficient_zero_iff S.xi hπ _ hne).mpr (h.2.2 i))

theorem absoluteLeadingHom_equivariant (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n)
    (σ' : Gal(k/F)) (g : congruenceSubgroup S n) :
    let a := absoluteLeadingHom S hn
    let z := (a g).toAdd
    (a ⟨S.action σ' g, congruenceSubgroup_stable S hn σ' g⟩).toAdd =
      (fun i => residueAction S σ' (z.1 i), fun χ => residueAction S σ' (z.2.1 χ),
        fun i => residueAction S σ' (z.2.2 i)) := by
  let C := X.comparison.chart
  let O := localIntegers S.E
  let e := S.integralCoefficient σ'
  let f : O ⟶ O := integralRingMap e.toRingHom
  let g' : congruenceSubgroup S n := ⟨S.action σ' g, congruenceSubgroup_stable S hn σ' g⟩
  let z := congruenceCoordinates S hn g
  let hz := (congruenceCoordinates_spec S hn g).2
  let z' := congruenceCoordinates S hn g'
  let hz' := (congruenceCoordinates_spec S hn g').2
  let h := markedCellChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates
  have he : z' = mapCellValues f z := by
    apply h.1 O
    exact (congruenceCoordinates_spec S hn g').1.trans
      ((S.point_equivariant σ' g).trans ((congrArg (changeRingHom M.group f)
        (congruenceCoordinates_spec S hn g).1.symm).trans (h.2 f z)))
  have hfix : e S.xi = S.xi :=
    Subtype.ext ((S.integralCoefficient_eq σ' S.xi).trans (S.coefficient_fixes_xi σ'))
  have hne : S.xi ≠ 0 := fun h => S.xi_uniformizer.ne_zero (congrArg Subtype.val h)
  let v := leadingEntries S n z hz
  change leadingEntries S n z' hz' =
    (fun i => residueAction S σ' (v.1 i), fun χ => residueAction S σ' (v.2.1 χ),
      fun i => residueAction S σ' (v.2.2 i))
  let hπ := S.xi_uniformizer.is_generator
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun χ => ?_) (funext fun i => ?_))
  · exact leadingCoefficient_map S.xi hπ ⟨z.1 i, hz.1 i⟩ hne e hfix
      ⟨z'.1 i, hz'.1 i⟩ (congrArg (fun z => z.1 i) he)
  · apply leadingCoefficient_map S.xi hπ ⟨(z.2.1 χ : O) - 1, hz.2.1 χ⟩ hne e hfix
      ⟨(z'.2.1 χ : O) - 1, hz'.2.1 χ⟩
    have hc : (z'.2.1 χ : O) = e (z.2.1 χ : O) :=
      congrArg (fun z : CellValues D O C.negative C.positive => (z.2.1 χ : O)) he
    change (z'.2.1 χ : O) - 1 = e ((z.2.1 χ : O) - 1)
    rw [hc, map_sub, map_one]
  · exact leadingCoefficient_map S.xi hπ ⟨z.2.2 i, hz.2.2 i⟩ hne e hfix
      ⟨z'.2.2 i, hz'.2.2 i⟩ (congrArg (fun z => z.2.2 i) he)

end ScaledFace

section PointTopology

open IntegralSemisimpleModel ExceptionalIwahoriCongruence Opposite WithConv
open ValuativeRel

universe u

private theorem pointAlgebra_changeRing (B : IntegralAlgebra.{u}) {X : IntegralScheme.{u}}
    (iso : integralSpec.obj (op B) ≅ X) {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (p : integralSpec.obj (op R) ⟶ X) :
    (pointAlgebraEquiv B iso S).symm (changeRing f p) =
      f.hom.comp ((pointAlgebraEquiv B iso R).symm p) := by
  obtain ⟨a, rfl⟩ := (pointAlgebraEquiv B iso R).surjective p
  rw [Equiv.symm_apply_apply]
  apply (pointAlgebraEquiv B iso S).injective
  rw [Equiv.apply_symm_apply]
  change integralSpec.map f.op ≫ integralSpec.map (CommAlgCat.ofHom a).op ≫ iso.hom =
    integralSpec.map (CommAlgCat.ofHom (f.hom.comp a)).op ≫ iso.hom
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

private theorem pointAlgebra_changePresentation (B C : IntegralAlgebra.{u})
    {X : IntegralScheme.{u}}
    (b : integralSpec.obj (op B) ≅ X) (c : integralSpec.obj (op C) ≅ X) :
    ∃ f : C →ₐ[Integers.{u}] B, ∀ (R : IntegralAlgebra.{u})
      (p : integralSpec.obj (op R) ⟶ X),
      (pointAlgebraEquiv C c R).symm p = ((pointAlgebraEquiv B b R).symm p).comp f := by
  let S := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let f := S.preimage (b.hom ≫ c.inv)
  have hf : integralSpec.map f = b.hom ≫ c.inv := S.map_preimage _
  refine ⟨f.unop.hom, fun R p => ?_⟩
  obtain ⟨a, rfl⟩ := (pointAlgebraEquiv B b R).surjective p
  rw [Equiv.symm_apply_apply]
  apply (pointAlgebraEquiv C c R).injective
  rw [Equiv.apply_symm_apply]
  change integralSpec.map (CommAlgCat.ofHom a).op ≫ b.hom =
    integralSpec.map (CommAlgCat.ofHom (a.comp f.unop.hom)).op ≫ c.hom
  rw [show (CommAlgCat.ofHom (a.comp f.unop.hom)).op = (CommAlgCat.ofHom a).op ≫ f by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    rfl]
  simp [hf, Category.assoc]

private theorem continuous_markedPoints_iff {P : Type*} [TopologicalSpace P]
    {K : Type u} [Field K] [TopologicalSpace K] {X : IntegralScheme.{u}}
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ X)
    (f : P → (integralSpec.obj (op (integralRing K)) ⟶ X)) :
    letI := markedPointTopology B iso K
    Continuous f ↔ ∀ a : B, Continuous fun z =>
      (pointAlgebraEquiv B iso (integralRing K)).symm (f z) a := by
  change @Continuous _ _ _ (TopologicalSpace.induced _ (TopologicalSpace.induced _ _)) f ↔ _
  rw [continuous_induced_rng, continuous_induced_rng, continuous_pi_iff]
  rfl

private theorem continuous_markedEvaluation
    {K : Type u} [Field K] [TopologicalSpace K] {X : IntegralScheme.{u}}
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ X) (b : B) :
    letI := markedPointTopology B iso K
    Continuous (fun p : integralSpec.obj (op (integralRing K)) ⟶ X =>
      (pointAlgebraEquiv B iso (integralRing K)).symm p b) := by
  letI := markedPointTopology B iso K
  exact (continuous_markedPoints_iff (K := K) B iso
    (@id (integralSpec.obj (op (integralRing K)) ⟶ X))).mp continuous_id b

/-- A continuous field embedding gives a continuous scalar map in the
marked point topology. -/
theorem continuous_markedChangeRing {K E : Type u} [Field K] [Field E]
    [TopologicalSpace K] [TopologicalSpace E]
    (f : K →+* E) (hf : Continuous f) {X : IntegralScheme.{u}}
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ X) :
    letI := markedPointTopology B iso K
    letI := markedPointTopology B iso E
    Continuous (changeRing (integralRingMap f) (X := X)) := by
  letI := markedPointTopology B iso K
  letI := markedPointTopology B iso E
  apply (continuous_markedPoints_iff B iso _).mpr
  intro b
  letI : Algebra Integers.{u} E := (integralRing E).algebra
  have he (p : integralSpec.obj (op (integralRing K)) ⟶ X) :
      (pointAlgebraEquiv B iso (integralRing E)).symm (changeRing (integralRingMap f) p) b =
        f ((pointAlgebraEquiv B iso (integralRing K)).symm p b) :=
    congrArg (fun a : B →ₐ[Integers.{u}] E => a b)
      (pointAlgebra_changeRing B iso (integralRingMap f) p)
  simpa only [he, Function.comp_def] using hf.comp (continuous_markedEvaluation B iso b)

open ExceptionalLocalRootCoordinates (normalizedValuation)
open scoped Topology

private theorem continuous_of_valuation_power {K E : Type*} [Field K] [Field E]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    (f : K →+* E) {d : ℕ} (hd : 0 < d)
    (hf : ∀ x, normalizedValuation E (f x) = normalizedValuation K x ^ d) :
    Continuous f := by
  apply continuous_of_continuousAt_zero f
  change Filter.Tendsto f (𝓝 (0 : K)) (𝓝 (f 0))
  rw [map_zero]
  apply ((IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' E)).mpr
  intro radius hradius
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  let k := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let a := min 1 (e radius)
  have ha : a ≠ 0 := ne_of_gt
    (lt_min (by simp) (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hradius)))
  refine ⟨k.symm a, (map_ne_zero _).mpr ha, fun z hz => ?_⟩
  have hz' : normalizedValuation K z < a := by
    change valuation K z < k.symm a at hz
    have h := k.strictMono hz
    rwa [k.apply_symm_apply] at h
  change valuation E (f z) < radius
  apply e.strictMono.lt_iff_lt.mp
  change normalizedValuation E (f z) < e radius
  rw [hf]
  apply lt_of_le_of_lt _ (hz'.trans_le (min_le_right _ _))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [pow_succ']
  exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (hz'.le.trans (min_le_left _ _)))

private theorem isClosed_valuationIdealPower {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (n : ℕ) :
    IsClosed (Set.range fun z : ↥(IsLocalRing.maximalIdeal ((valuation K).valuationSubring) ^ n) =>
      ((z : (valuation K).valuationSubring) : K)) := by
  let O := (valuation K).valuationSubring
  letI : CompactSpace O := inferInstanceAs (CompactSpace (Valuation.integer (valuation K)))
  have he : (Set.range fun z : ↥(IsLocalRing.maximalIdeal O ^ n) => ((z : O) : K)) =
      Set.range (fun b : O => (π : K) ^ n * (b : K)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff_factor π hπ.is_generator n (a : O)).mp a.2
      exact ⟨b, (congrArg (fun z : O => (z : K)) hb).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨π ^ n * b, (mem_maximalIdeal_pow_iff_factor π hπ.is_generator n _).mpr ⟨b, rfl⟩⟩, rfl⟩
  rw [he]
  exact (isCompact_range (continuous_const.mul (continuous_subtype_val : Continuous fun b : O => (b : K)))).isClosed

private theorem isClosed_pointReductionKernel {P : Type*} [Group P] [TopologicalSpace P]
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (G : IntegralGroup.{u}) (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ G.X)
    (p : P →* IntegralPoints G (localIntegers K))
    (hcont : letI := markedPointTopology B iso K
      Continuous (fun g => changeRingHom G (localIntegersInclusion K) (p g))) (n : ℕ) :
    IsClosed (((changeRingHom G (congruenceHom (localIntegers K) n)).comp p).ker : Set P) := by
  let O := localIntegers K
  letI : Algebra Integers.{u} K := (integralRing K).algebra
  let I := IsLocalRing.maximalIdeal O ^ n
  let f := congruenceHom O n
  let j := localIntegersInclusion K
  let i := pointAlgebraEquiv B iso (integralRing K)
  let q (a : B) (g : P) := i.symm (changeRingHom G j (p g)) a
  let Z : Set K := Set.range fun z : I => ((z : O) : K)
  have hZ : IsClosed Z := isClosed_valuationIdealPower π hπ n
  have hl (b : O) : (b : K) ∈ Z ↔ b ∈ I := by
    constructor
    · rintro ⟨a, ha⟩
      obtain rfl : (a : O) = b := Subtype.ext ha
      exact a.2
    · intro hb
      exact ⟨⟨b, hb⟩, rfl⟩
  have hq (a : B) (g : P) : q a g = ((pointAlgebraEquiv B iso O).symm (p g) a : K) :=
    congrArg (fun f : B →ₐ[Integers.{u}] K => f a)
      (pointAlgebra_changeRing B iso j (p g))
  have hR : (((changeRingHom G f).comp p).ker : Set P) =
      ⋂ a : B, (fun g => q a g - q a 1) ⁻¹' Z := by
    ext g
    change changeRingHom G f (p g) = 1 ↔ _
    have hone : changeRingHom G f (p 1) = 1 := by
      exact (congrArg (changeRingHom G f) (p.map_one)).trans ((changeRingHom G f).map_one)
    rw [← hone]
    rw [← (pointAlgebraEquiv B iso (congruenceRing O n)).symm.injective.eq_iff]
    change (pointAlgebraEquiv B iso _).symm (changeRing f (p g)) =
      (pointAlgebraEquiv B iso _).symm (changeRing f (p 1)) ↔ _
    rw [pointAlgebra_changeRing, pointAlgebra_changeRing, AlgHom.ext_iff, Set.mem_iInter]
    simp only [Set.mem_preimage, AlgHom.comp_apply, hq]
    apply forall_congr'
    intro a
    let x := (pointAlgebraEquiv B iso O).symm (p g) a
    let y := (pointAlgebraEquiv B iso O).symm (p 1) a
    change Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ (((x - y : O) : K) ∈ Z)
    exact Ideal.Quotient.eq.trans (hl (x - y)).symm
  rw [hR]
  refine isClosed_iInter fun a => hZ.preimage ?_
  letI := markedPointTopology B iso K
  exact ((continuous_markedEvaluation B iso a).comp hcont).sub continuous_const

end PointTopology

section ScaledFaceTopology

open _root_.LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceCongruence
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel ExceptionalIwahoriCongruence Opposite
open ExceptionalValuedTorusNormalizer (invariantApartment)
open ExceptionalLocalRootCoordinates (normalizedValuation)

universe u

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} {T : DiagramCompositum F L k σ} {A : FoldedApartment (R.diagram σ)}
    {X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A}
    {J : Set (A.roots.SimpleWall A.basepoint)} {x : invariantApartment D (R.diagram σ)}

/-- The unramified coefficient action is continuous on the actual marked
parahoric with the topology induced by its marked field points. -/
theorem continuous_parahoricCoefficient (S : ScaledFace T X J x)
    (hX : X.Coefficients T) (B : IntegralAlgebra.{u})
    (iso : integralSpec.obj (op B) ≅ M.group.X) (γ' : Gal(k/F)) :
    letI := TopologicalSpace.induced X.points (markedPointTopology B iso T.field)
    Continuous (S.action γ' : parahoric X.comparison J → parahoric X.comparison J) := by
  let G := GroupPoints R.descent.group.val (CommAlgCat.of F k)
  letI : TopologicalSpace (FieldPoints M T.field) := markedPointTopology B iso T.field
  letI : TopologicalSpace G := TopologicalSpace.induced X.points (markedPointTopology B iso T.field)
  let f := (T.coefficient γ').toRingHom
  have hval (z : T.field) : normalizedValuation T.field (f z) = normalizedValuation T.field z := by
    have h := normalizedValuation_fixed_uniformizer S.xi S.xi_uniformizer (S.coefficient γ')
      (S.coefficient_fixes_xi γ') (S.integralCoefficient γ') (S.integralCoefficient_eq γ')
      (algebraMap T.field S.E z)
    rw [S.coefficient_extends, auxiliaryValuation S, auxiliaryValuation S] at h
    exact (pow_left_inj₀ zero_le zero_le S.d_pos.ne').mp h
  have hcont : Continuous f :=
    continuous_of_valuation_power f (d := 1) Nat.one_pos (fun z => by rw [pow_one, hval])
  obtain ⟨a, ha, hpt, _⟩ := hX
  have h (g : parahoric X.comparison J) :
      X.points (S.action γ' g : parahoric X.comparison J) =
        scalarPoints M f (X.points g) := by
    rw [S.action_eq, ← ha]
    exact hpt γ' g
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  have hpt : Continuous (X.points : G → FieldPoints M T.field) := continuous_induced_dom
  change Continuous (fun g : parahoric X.comparison J =>
    X.points (S.action γ' g : parahoric X.comparison J))
  rw [show (fun g : parahoric X.comparison J => X.points (S.action γ' g : parahoric X.comparison J)) =
    (fun g : parahoric X.comparison J => scalarPoints M f (X.points g)) from funext h]
  exact (continuous_markedChangeRing f hcont B iso).comp
    (hpt.comp (continuous_subtype_val (p := fun g => g ∈ parahoric X.comparison J)))

end ScaledFaceTopology


section CoordinateLayers

open _root_.LinearAlgebraicGroups.Specs.RamifiedExceptionalFaceCongruence
open _root_.LinearAlgebraicGroups.Specs.RamifiedCongruenceCoefficientDepths
  (AtDepth SingleSlot PairedSlots scaledEntry pairedFactor AuxiliaryScaling)
open _root_.LinearAlgebraicGroups.Specs.RamifiedCongruenceTorusCoordinates
  (simpleUnit orbitValues fieldUnit)
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel ExceptionalIwahoriCongruence Opposite
open ExceptionalValuedTorusNormalizer (invariantApartment)
open ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex)
open ExceptionalAffineRootSystems (FoldedRootDirection IsLongF4Doubled e6Partner)
open ValuativeRel IsLocalRing

universe u

attribute [local instance] integerAlgebra ExceptionalLocalRootCoordinates.canonicalExtension

local notation "O(" K ")" => Valuation.valuationSubring (ValuativeRel.valuation K)
local notation "κ(" K ")" => IsLocalRing.ResidueField (O(K))
local notation "FieldLeading" =>
  LinearAlgebraicGroups.Specs.RamifiedCongruenceCoefficientDepths.IsLeading

private theorem fieldLeading_atDepth {E : Type*} [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {ξ : O(E)} (hξ : (valuation E).IsUniformizer (ξ : E))
    {n : ℕ} {z : E} {r : κ(E)} (hz : FieldLeading ξ n z r) : AtDepth n z := by
  obtain ⟨c, h, _⟩ := hz
  exact ⟨ξ ^ n * c, (mem_maximalIdeal_pow_iff_factor ξ hξ.is_generator n _).mpr ⟨c, rfl⟩,
    h.symm⟩

private theorem fieldLeading_unique {E : Type*} [Field E] [ValuativeRel E]
    {ξ : O(E)} (hξ : (ξ : E) ≠ 0) {n : ℕ} {z : E} {r t : κ(E)}
    (hr : FieldLeading ξ n z r) (ht : FieldLeading ξ n z t) : r = t := by
  obtain ⟨b, hb, rfl⟩ := hr
  obtain ⟨c, hc, rfl⟩ := ht
  exact congrArg (residue _) (Subtype.ext (mul_left_cancel₀ (pow_ne_zero n hξ) (hb.symm.trans hc)))

private theorem fieldLeading_zero {E : Type*} [Field E] [ValuativeRel E]
    (ξ : O(E)) (n : ℕ) : FieldLeading ξ n 0 0 :=
  ⟨0, by simp, map_zero _⟩

private theorem singleSlot_zero_of_inactive {P E : Type*} [Field P] [Field E]
    [ValuativeRel P] [ValuativeRel E] [TopologicalSpace P] [TopologicalSpace E]
    [IsNonarchimedeanLocalField P] [IsNonarchimedeanLocalField E]
    {f : P →+* E} {ξ : O(E)} (hξ : (valuation E).IsUniformizer (ξ : E))
    {e n : ℕ} {s : ℤ} {c : O(E)ˣ} (H : SingleSlot f ξ e n s c)
    {a : P} {r : κ(E)} (hr : FieldLeading ξ n (scaledEntry f ξ s c a) r)
    (h : ¬ ∃ m : ℤ, (n : ℤ) = s + (e : ℤ) * m) : r = 0 :=
  fieldLeading_unique hξ.ne_zero hr (H.2.2.1 h a (fieldLeading_atDepth hξ hr))

private theorem singleSlot_lift {P E : Type*} [Field P] [Field E]
    [ValuativeRel P] [ValuativeRel E] [TopologicalSpace P] [TopologicalSpace E]
    [IsNonarchimedeanLocalField P] [IsNonarchimedeanLocalField E]
    {f : P →+* E} {ξ : O(E)} {e n : ℕ} {s : ℤ} {c : O(E)ˣ}
    (H : SingleSlot f ξ e n s c) (r : κ(E))
    (hr : (¬ ∃ m : ℤ, (n : ℤ) = s + (e : ℤ) * m) → r = 0) :
    ∃ a, FieldLeading ξ n (scaledEntry f ξ s c a) r := by
  by_cases h : ∃ m : ℤ, (n : ℤ) = s + (e : ℤ) * m
  · obtain ⟨m, hm⟩ := h
    obtain ⟨a, ha, _⟩ := H.2.2.2 m hm r
    exact ⟨a, ha⟩
  · exact ⟨0, by simpa [scaledEntry, hr h] using fieldLeading_zero ξ n⟩

private theorem singleSlot_lift_unit {P E : Type*} [Field P] [Field E]
    [ValuativeRel P] [ValuativeRel E] [TopologicalSpace P] [TopologicalSpace E]
    [IsNonarchimedeanLocalField P] [IsNonarchimedeanLocalField E]
    {f : P →+* E} {ξ : O(E)} {e n : ℕ}
    (H : SingleSlot f ξ e n 0 1) (r : κ(E))
    (hr : (¬ ∃ m : ℤ, (n : ℤ) = (e : ℤ) * m) → r = 0) :
    ∃ t : Pˣ, FieldLeading ξ n (f (t : P) - 1) r := by
  by_cases h : ∃ m : ℤ, (n : ℤ) = (e : ℤ) * m
  · obtain ⟨m, hm⟩ := h
    obtain ⟨a, ha, _, _, hu⟩ := H.2.2.2 m (by simpa using hm) r
    obtain ⟨t, ht⟩ := hu rfl
    refine ⟨fieldUnit t, ?_⟩
    change FieldLeading ξ n (f ((t : O(P)) : P) - 1) r
    rw [← map_one f, ← map_sub, ht]
    simpa [scaledEntry] using ha
  · exact ⟨1, by simpa [hr h] using fieldLeading_zero ξ n⟩

private def pairFactorAt {K E : Type*} [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
    (ε : O(K)ˣ) (d n : ℕ) (s : ℤ) (c₁ c₂ : O(E)ˣ) : κ(E)ˣ := by
  classical
  exact if h : ∃ m : ℤ, (n : ℤ) = s + (d : ℤ) * m then pairedFactor c₁ c₂ ε h.choose else 1

private theorem pairedSlot_leading {K E : Type*} [Field K] [Field E] [Algebra K E]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
    {τ : K ≃+* K} {ξ : O(E)} (hξ : (valuation E).IsUniformizer (ξ : E))
    {ε : O(K)ˣ} {d n : ℕ} {s : ℤ} {c₁ c₂ : O(E)ˣ} (H : PairedSlots τ ξ ε d n s c₁ c₂)
    {a : K} {r : κ(E)} (hr : FieldLeading ξ n (scaledEntry (algebraMap K E) ξ s c₁ a) r) :
    ((¬ ∃ m : ℤ, (n : ℤ) = s + (d : ℤ) * m) → r = 0) ∧
    FieldLeading ξ n (scaledEntry ((algebraMap K E).comp τ.toRingHom) ξ s c₂ a)
      ((pairFactorAt ε d n s c₁ c₂ : κ(E)) * r) := by
  classical
  by_cases h : ∃ m : ℤ, (n : ℤ) = s + (d : ℤ) * m
  · exact ⟨fun h' => (h' h).elim,
      by simpa [pairFactorAt, h] using (H.2.2 h.choose h.choose_spec).1 a r hr⟩
  · obtain ⟨h₁, h₂⟩ := H.2.1 h a (fieldLeading_atDepth hξ hr)
    have he := fieldLeading_unique hξ.ne_zero hr h₁
    exact ⟨fun _ => he, by simpa [he] using h₂⟩

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
    {σ : Gal(L/F)} {T : DiagramCompositum F L k σ} {A : FoldedApartment (R.diagram σ)}
    {X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A}
    {J : Set (A.roots.SimpleWall A.basepoint)} {x : invariantApartment D (R.diagram σ)}

private abbrev ChartCell
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (B : IntegralAlgebra.{u}) :=
  CellValues D B X.comparison.chart.negative X.comparison.chart.positive

private abbrev RootSlot
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A) :=
  Fin X.comparison.chart.negative.length ⊕ Fin X.comparison.chart.positive.length

private def rootSlotIndex
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A) :
    RootSlot X → D.I
  | .inl i => X.comparison.chart.negative[i]
  | .inr i => X.comparison.chart.positive[i]

private theorem rootSlotIndex_bijective : Function.Bijective (rootSlotIndex X) := by
  let C := X.comparison.chart
  have hn (i : Fin C.negative.length) : ¬ D.base.IsPos C.negative[i] :=
    (C.negative_enumerates.2 _).mp (List.get_mem _ _)
  have hp (i : Fin C.positive.length) : D.base.IsPos C.positive[i] :=
    (C.positive_enumerates.2 _).mp (List.get_mem _ _)
  constructor
  · rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (C.negative_enumerates.1.injective_get h)
    · change C.negative[i] = C.positive[j] at h
      exact (hn i (h.symm ▸ hp j)).elim
    · change C.positive[i] = C.negative[j] at h
      exact (hn j (h ▸ hp i)).elim
    · exact congrArg Sum.inr (C.positive_enumerates.1.injective_get h)
  · intro i
    by_cases h : D.base.IsPos i
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((C.positive_enumerates.2 i).mpr h)
      exact ⟨.inr j, hj⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((C.negative_enumerates.2 i).mpr h)
      exact ⟨.inl j, hj⟩

private abbrev RootFiber
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)
    (a : FoldedRootDirection) := {j : RootSlot X // A.direction (rootSlotIndex X j) = a}

private def rootCellEntry {B : IntegralAlgebra.{u}} (z : ChartCell X B) : RootSlot X → B :=
  Sum.elim z.1 z.2.2

private def rootLeadingEntry (S : ScaledFace T X J x) (v : AbsoluteLeadingVectors S) :
    RootSlot X → κ(S.E) := Sum.elim v.1 v.2.2

private def rootSlotUnit
    (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A) :
    RootSlot X → Integers.{u}ˣ :=
  Sum.elim X.comparison.chart.chart.negUnit X.comparison.chart.chart.posUnit

private def rootSlotMap {a : FoldedRootDirection} (j : RootFiber X a) :
    X.comparison.chart.parameter a →+* T.field := by
  let C := X.comparison.chart
  rcases j with ⟨i | i, hi⟩
  · have h : C.chart.neg i = a :=
      (C.neg_slots i).trans ((congrFun X.directions _).trans hi)
    exact h ▸ C.chart.negMap i
  · have h : C.chart.pos i = a :=
      (C.pos_slots i).trans ((congrFun X.directions _).trans hi)
    exact h ▸ C.chart.posMap i

private theorem castRingHom_apply {Q : FoldedRootDirection → Type u}
    [∀ a, Field (Q a)] {a b : FoldedRootDirection} (h : a = b) (f : Q a →+* T.field)
    (v : Q b) : (h ▸ f) v = f (h.symm ▸ v) := by
  subst b
  rfl

private theorem rootSlotMap_eq_of_uses {i : D.I} {a : FoldedRootDirection}
    {f : X.comparison.chart.parameter a →+* T.field}
    (h : X.comparison.chart.UsesSlot i a f) (j : RootFiber X a)
    (hj : rootSlotIndex X j.val = i) : rootSlotMap j = f := by
  apply RingHom.ext
  intro p
  rcases j with ⟨l | l, hl⟩
  · have h' := (X.comparison.chart.neg_slots l).trans ((congrFun X.directions _).trans hl)
    exact (castRingHom_apply h' _ _).trans (h.2.1 l h' p hj)
  · have h' := (X.comparison.chart.pos_slots l).trans ((congrFun X.directions _).trans hl)
    exact (castRingHom_apply h' _ _).trans (h.2.2 l h' p hj)

private theorem rootSlotMap_coordinates {a : FoldedRootDirection} (j : RootFiber X a)
    (v : ∀ a, X.comparison.chart.parameter a) (t : X.comparison.chart.chart.torus) :
    rootCellEntry (X := X) (X.comparison.chart.chart.coordinates t v) j.val =
      algebraMap Integers.{u} T.field (rootSlotUnit X j.val : Integers.{u}) * rootSlotMap j (v a) := by
  have transport {b c : FoldedRootDirection} (h : b = c) : h.symm ▸ v c = v b := by
    subst c
    rfl
  rcases j with ⟨l | l, hl⟩
  · have h' := (X.comparison.chart.neg_slots l).trans ((congrFun X.directions _).trans hl)
    exact congrArg (_ * ·) ((castRingHom_apply h' _ _).trans (congrArg _ (transport h'))).symm
  · have h' := (X.comparison.chart.pos_slots l).trans ((congrFun X.directions _).trans hl)
    exact congrArg (_ * ·) ((castRingHom_apply h' _ _).trans (congrArg _ (transport h'))).symm

private def integralMarkingUnit (S : ScaledFace T X J x) (c : Integers.{u}ˣ) : O(S.E)ˣ :=
  Units.map ((Int.castRingHom O(S.E)).comp ULift.ringEquiv.toRingHom).toMonoidHom c

private theorem integralMarkingUnit_val (S : ScaledFace T X J x) (c : Integers.{u}ˣ) :
    (((integralMarkingUnit S c : O(S.E)ˣ) : O(S.E)) : S.E) =
      algebraMap T.field S.E (algebraMap Integers.{u} T.field (c : Integers.{u})) := by
  change ((c : Integers.{u}).down : S.E) =
    algebraMap T.field S.E ((c : Integers.{u}).down : T.field)
  exact (map_intCast (algebraMap T.field S.E) _).symm

private def scaledFieldCell (S : ScaledFace T X J x) (z : ChartCell X (integralRing T.field)) :
    ChartCell X (integralRing S.E) :=
  scaleCellValues (cocharacter D S.cocharacter (integralRing S.E)
    (Units.mk0 (S.xi : S.E) S.xi_uniformizer.ne_zero))
    (mapCellValues (integralRingMap (algebraMap T.field S.E)) z)

private def scaledRootEntry (S : ScaledFace T X J x) {a : FoldedRootDirection}
    (j : RootFiber X a) : X.comparison.chart.parameter a → S.E :=
  scaledEntry ((algebraMap T.field S.E).comp (rootSlotMap j)) S.xi (rootShift S a)
    (integralMarkingUnit S (rootSlotUnit X j.val))

private theorem rootShift_eq (S : ScaledFace T X J x) (i : D.I) :
    D.datum.toLinearMap (D.datum.root i) S.cocharacter = rootShift S (A.direction i) := by
  apply Int.cast_injective (α := ℚ)
  rw [rootScalingExponent S i]
  let i' := (A.surjective (A.direction i)).choose
  have h := rootScalingExponent S i'
  change (_ : ℚ) = _ at h
  rw [(A.surjective (A.direction i)).choose_spec] at h
  exact h.symm

private theorem scaledFieldCell_root (S : ScaledFace T X J x)
    (t : X.comparison.chart.chart.torus) (v : ∀ a, X.comparison.chart.parameter a)
    {a : FoldedRootDirection} (j : RootFiber X a) :
    rootCellEntry (X := X) (scaledFieldCell S (X.comparison.chart.chart.coordinates t v)) j.val =
      scaledRootEntry S j (v a) := by
  let C := X.comparison.chart
  let f := algebraMap T.field S.E
  have hshift : D.datum.toLinearMap (D.datum.root (rootSlotIndex X j.val)) S.cocharacter = rootShift S a :=
    (rootShift_eq S _).trans (congrArg (rootShift S) j.property)
  have hcoord := rootSlotMap_coordinates j v t
  have h₀ : rootCellEntry (X := X) (scaledFieldCell S (C.chart.coordinates t v)) j.val =
      (S.xi : S.E) ^ D.datum.toLinearMap (D.datum.root (rootSlotIndex X j.val)) S.cocharacter *
        f (rootCellEntry (X := X) (C.chart.coordinates t v) j.val) := by
    rcases j with ⟨i | i, hi⟩ <;>
      simp only [rootCellEntry, rootSlotIndex, Sum.elim_inl, Sum.elim_inr, scaledFieldCell,
        scaleCellValues, mapCellValues, cocharacter, MonoidHom.coe_mk, OneHom.coe_mk,
        Units.val_zpow_eq_zpow_val, Units.val_mk0, f] <;> rfl
  rw [h₀, hshift, hcoord, map_mul]
  simp only [scaledRootEntry, scaledEntry, integralMarkingUnit_val, RingHom.comp_apply, f, mul_assoc]

private def SlotCoefficients (S : ScaledFace T X J x) (ε : O(T.field)ˣ) (n : ℕ) : Prop :=
  ∀ (s : ℤ) (c₁ c₂ : O(S.E)ˣ),
    SingleSlot ((algebraMap T.field S.E).comp (algebraMap k T.field)) S.xi (2 * S.d) n s c₁ ∧
    SingleSlot (algebraMap T.field S.E) S.xi S.d n s c₁ ∧
    PairedSlots T.diagram.toRingEquiv S.xi ε S.d n s c₁ c₂

private abbrev RootActive (S : ScaledFace T X J x) (n : ℕ) (a : FoldedRootDirection) :=
  ∃ m : ℤ, (n : ℤ) = rootShift S a + rootStep S a * m

/-- At a fixed depth, one absolute entry determines the leading terms of a root orbit. -/
private structure RootOrbitLayer (S : ScaledFace T X J x) (n : ℕ) (a : FoldedRootDirection) where
  representative : RootFiber X a
  factor : RootFiber X a → κ(S.E)ˣ
  factor_representative : factor representative = 1
  compare (p : X.comparison.chart.parameter a) (r : κ(S.E))
      (hr : FieldLeading S.xi n (scaledRootEntry S representative p) r) :
    (¬ RootActive S n a → r = 0) ∧
      ∀ j, FieldLeading S.xi n (scaledRootEntry S j p) ((factor j : κ(S.E)) * r)
  lift (r : κ(S.E)) (hr : ¬ RootActive S n a → r = 0) :
    ∃ p, FieldLeading S.xi n (scaledRootEntry S representative p) r

private theorem rootOrbitLayer_exists (S : ScaledFace T X J x) {ε : O(T.field)ˣ} {n : ℕ}
    (H : SlotCoefficients S ε n) (a : FoldedRootDirection) : Nonempty (RootOrbitLayer S n a) := by
  classical
  let K := T.field
  let E := S.E
  let s := rootShift S a
  let mark (j : RootFiber X a) := integralMarkingUnit S (rootSlotUnit X j.val)
  have index_inj := (rootSlotIndex_bijective (X := X)).1
  have index_surj := (rootSlotIndex_bijective (X := X)).2
  by_cases ha : IsLongF4Doubled a.val
  · obtain ⟨i, hi⟩ := A.surjective a
    have hfix : (R.diagram σ).val.indexEquiv i = i := (A.long i).mp (hi.symm ▸ ha)
    obtain ⟨e, he, _⟩ := X.singleton i hfix
    obtain ⟨j, hj⟩ := index_surj i
    let rep : RootFiber X a := ⟨j, (congrArg A.direction hj).trans hi⟩
    have hrep (p : X.comparison.chart.parameter a) : scaledRootEntry S rep p =
        scaledEntry ((algebraMap K E).comp (algebraMap k K)) S.xi s (mark rep)
          (e (hi.symm ▸ p)) := by
      subst a
      rw [scaledRootEntry, rootSlotMap_eq_of_uses he rep hj]
      rfl
    have hsub (j' : RootFiber X a) : j' = rep := by
      apply Subtype.ext
      apply index_inj
      rw [hj]
      rcases (A.orbits i (rootSlotIndex X j'.val)).mp (hi.trans j'.property.symm) with h | h
      · exact h
      · exact h.trans hfix
    have hact : RootActive S n a ↔ ∃ m : ℤ, (n : ℤ) = s + ((2 * S.d : ℕ) : ℤ) * m := by
      simp [RootActive, rootStep, ha, s, mul_comm]
    have H₁ := (H s (mark rep) 1).1
    refine ⟨⟨rep, fun _ => 1, rfl, ?_, ?_⟩⟩
    · intro p r hr
      rw [hrep] at hr
      refine ⟨fun h => singleSlot_zero_of_inactive S.xi_uniformizer H₁ hr (h ∘ hact.mpr), ?_⟩
      intro j'
      rw [hsub j', hrep]
      simpa using hr
    · intro r hr
      obtain ⟨v, hv⟩ := singleSlot_lift H₁ r (fun h => hr (h ∘ hact.mp))
      refine ⟨hi ▸ e.symm v, ?_⟩
      rw [hrep]
      subst a
      simpa using hv
  · obtain ⟨i, hi, e, he, he', _⟩ := X.pair a ha
    let i' := (R.diagram σ).val.indexEquiv i
    have hi' : A.direction i' = a := ((A.orbits i i').mpr (Or.inr rfl)).symm.trans hi
    have hne : i' ≠ i := fun h => ha (hi ▸ (A.long i).mpr h)
    obtain ⟨j, hj⟩ := index_surj i
    obtain ⟨j', hj'⟩ := index_surj i'
    let rep : RootFiber X a := ⟨j, (congrArg A.direction hj).trans hi⟩
    let partner : RootFiber X a := ⟨j', (congrArg A.direction hj').trans hi'⟩
    have hpr : partner ≠ rep := by
      intro h
      exact hne (hj'.symm.trans ((congrArg (fun z : RootFiber X a => rootSlotIndex X z.val) h).trans hj))
    have hrep (p : X.comparison.chart.parameter a) : scaledRootEntry S rep p =
        scaledEntry (algebraMap K E) S.xi s (mark rep) (e p) := by
      rw [scaledRootEntry, rootSlotMap_eq_of_uses he rep hj]
      rfl
    have hpartner (p : X.comparison.chart.parameter a) : scaledRootEntry S partner p =
        scaledEntry ((algebraMap K E).comp T.diagram.toRingHom) S.xi s (mark partner) (e p) := by
      rw [scaledRootEntry, rootSlotMap_eq_of_uses he' partner hj']
      rfl
    have hcases (l : RootFiber X a) : l = rep ∨ l = partner := by
      rcases (A.orbits i _).mp (hi.trans l.property.symm) with hl | hl
      · exact Or.inl (Subtype.ext (index_inj (hl.trans hj.symm)))
      · exact Or.inr (Subtype.ext (index_inj (hl.trans hj'.symm)))
    have hact : RootActive S n a ↔ ∃ m : ℤ, (n : ℤ) = s + (S.d : ℤ) * m := by
      simp [RootActive, rootStep, ha, s]
    obtain ⟨_, H₁, H₂⟩ := H s (mark rep) (mark partner)
    let factor (l : RootFiber X a) : κ(E)ˣ :=
      if l = rep then 1 else pairFactorAt ε S.d n s (mark rep) (mark partner)
    refine ⟨⟨rep, factor, by simp [factor], ?_, ?_⟩⟩
    · intro p r hr
      rw [hrep] at hr
      obtain ⟨hz, hp⟩ := pairedSlot_leading S.xi_uniformizer H₂ hr
      refine ⟨fun h => hz (h ∘ hact.mpr), ?_⟩
      intro l
      rcases hcases l with rfl | rfl
      · simpa [factor, hrep] using hr
      · simpa [factor, hpr, hpartner] using hp
    · intro r hr
      obtain ⟨v, hv⟩ := singleSlot_lift H₁ r (fun h => hr (h ∘ hact.mp))
      exact ⟨e.symm v, by simpa [hrep] using hv⟩

private abbrev TorusActive (S : ScaledFace T X J x) (n : ℕ) (a : TorusOrbits) :=
  ∃ m : ℤ, (n : ℤ) = torusStep S a * m

private def torusFieldEntry (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (t : TorusValues D (integralRing T.field)) (i : Fin 6) : S.E :=
  algebraMap T.field S.E (simpleUnit b t i : T.field) - 1

private theorem torus_orbitValues (b : Fin 6 ≃ D.base.support) (hspan : D.datum.rootSpan ℤ = ⊤)
    (hdiagram : ∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i))
    (t : X.comparison.chart.chart.torus) :
    ∃ (a c : kˣ) (p q : T.fieldˣ),
      ∀ i, simpleUnit b t.val i = orbitValues T.diagram a c p q i := by
  have H := (RamifiedCongruenceTorusCoordinates.pinnedTorusCoordinates b hspan).2.2.2 R σ T X hdiagram
  have he := (H.2.1 t.val).mp t.property
  obtain ⟨a, ha, _⟩ := H.2.2.1 t 1 rfl
  obtain ⟨c, hc, _⟩ := H.2.2.1 t 3 rfl
  refine ⟨a, c, simpleUnit b t.val 0, simpleUnit b t.val 2, fun i => ?_⟩
  fin_cases i
  · rfl
  · exact ha.symm
  · rfl
  · exact hc.symm
  · exact he 2
  · exact he 0

private def torusLeadingFactor (S : ScaledFace T X J x) (ε : O(T.field)ˣ) (n : ℕ)
    (i : Fin 6) : κ(S.E)ˣ :=
  if i = 4 ∨ i = 5 then pairFactorAt ε S.d n 0 1 1 else 1

private theorem torusLeadingFactor_rep (S : ScaledFace T X J x) (ε : O(T.field)ˣ) (n : ℕ)
    (a : TorusOrbits) : torusLeadingFactor S ε n a.val = 1 := by
  obtain ⟨i, h⟩ := a
  have h4 : i ≠ 4 := fun e => (show ¬ (4 : Fin 6) ≤ e6Partner 4 by decide) (e ▸ h)
  have h5 : i ≠ 5 := fun e => (show ¬ (5 : Fin 6) ≤ e6Partner 5 by decide) (e ▸ h)
  simp [torusLeadingFactor, h4, h5]

/-- Read and lift the leading terms at the marked simple characters. -/
private structure TorusOrbitLayer (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (n : ℕ) where
  factor : Fin 6 → κ(S.E)ˣ
  factor_representative : ∀ a : TorusOrbits, factor a.val = 1
  compare (t : X.comparison.chart.chart.torus) (r : TorusOrbits → κ(S.E))
      (hr : ∀ a, FieldLeading S.xi n (torusFieldEntry S b t.val a.val) (r a)) :
    (∀ a, ¬ TorusActive S n a → r a = 0) ∧
    ∀ i, FieldLeading S.xi n (torusFieldEntry S b t.val i) ((factor i : κ(S.E)) * r (torusOrbit i))
  lift (r : TorusOrbits → κ(S.E)) (hr : ∀ a, ¬ TorusActive S n a → r a = 0) :
    ∃ t : X.comparison.chart.chart.torus,
      ∀ a, FieldLeading S.xi n (torusFieldEntry S b t.val a.val) (r a)

set_option maxHeartbeats 900000 in
private def torusOrbitLayer (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (hspan : D.datum.rootSpan ℤ = ⊤)
    (hdiagram : ∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i))
    {ε : O(T.field)ˣ} {n : ℕ} (H : SlotCoefficients S ε n) : TorusOrbitLayer S b n := by
  let f := algebraMap T.field S.E
  let g := (algebraMap T.field S.E).comp (algebraMap k T.field)
  have hsingle (i : Fin 6) (hi : i = 1 ∨ i = 3) :
      TorusActive S n (torusOrbit i) ↔ ∃ m : ℤ, (n : ℤ) = ((2 * S.d : ℕ) : ℤ) * m := by
    rcases hi with rfl | rfl <;>
      change (∃ m : ℤ, (n : ℤ) = ((S.d : ℤ) * 2) * m) ↔ _ <;> simp [mul_comm]
  have hpair (i : Fin 6) (hi : i = 0 ∨ i = 2) :
      TorusActive S n (torusOrbit i) ↔ ∃ m : ℤ, (n : ℤ) = (S.d : ℤ) * m := by
    rcases hi with rfl | rfl <;>
      change (∃ m : ℤ, (n : ℤ) = ((S.d : ℤ) * 1) * m) ↔ _ <;> simp
  obtain ⟨Hk, HK, HP⟩ := H 0 1 1
  refine ⟨torusLeadingFactor S ε n, torusLeadingFactor_rep S ε n, ?_, ?_⟩
  · intro t r hr
    obtain ⟨a, c, p, q, h⟩ := torus_orbitValues b hspan hdiagram t
    have he (i : Fin 6) : torusFieldEntry S b t.val i = f (orbitValues T.diagram a c p q i : T.field) - 1 :=
      congrArg (fun z : T.fieldˣ => f (z : T.field) - 1) (h i)
    have h₀ : FieldLeading S.xi n (f (p : T.field) - 1) (r (torusOrbit 0)) :=
      (he 0) ▸ hr (torusOrbit 0)
    have h₁ : FieldLeading S.xi n (g (a : k) - 1) (r (torusOrbit 1)) :=
      (he 1) ▸ hr (torusOrbit 1)
    have h₂ : FieldLeading S.xi n (f (q : T.field) - 1) (r (torusOrbit 2)) :=
      (he 2) ▸ hr (torusOrbit 2)
    have h₃ : FieldLeading S.xi n (g (c : k) - 1) (r (torusOrbit 3)) :=
      (he 3) ▸ hr (torusOrbit 3)
    have single {z : k} {r' : κ(S.E)} (hz : FieldLeading S.xi n (g z - 1) r')
        (h : ¬ ∃ m : ℤ, (n : ℤ) = ((2 * S.d : ℕ) : ℤ) * m) : r' = 0 := by
      apply singleSlot_zero_of_inactive S.xi_uniformizer Hk (a := z - 1)
      · simpa [scaledEntry, map_sub, g] using hz
      · simpa using h
    have pair {z : T.field} {r' : κ(S.E)} (hz : FieldLeading S.xi n (f z - 1) r') :
        ((¬ ∃ m : ℤ, (n : ℤ) = (S.d : ℤ) * m) → r' = 0) ∧
        FieldLeading S.xi n (f (T.diagram z) - 1)
          ((pairFactorAt ε S.d n 0 (1 : O(S.E)ˣ) 1 : κ(S.E)) * r') := by
      have hz' : FieldLeading S.xi n (scaledEntry f S.xi 0 1 (z - 1)) r' := by
        simpa [scaledEntry, map_sub] using hz
      obtain ⟨hzero, hother⟩ := pairedSlot_leading S.xi_uniformizer HP hz'
      exact ⟨fun h => hzero (by simpa using h), by simpa [scaledEntry, map_sub, f] using hother⟩
    have hp := pair h₀
    have hq := pair h₂
    constructor
    · rintro ⟨i, hi⟩ hainactive
      fin_cases i
      · exact hp.1 (hainactive ∘ (hpair 0 (Or.inl rfl)).mpr)
      · exact single h₁ (hainactive ∘ (hsingle 1 (Or.inl rfl)).mpr)
      · exact hq.1 (hainactive ∘ (hpair 2 (Or.inr rfl)).mpr)
      · exact single h₃ (hainactive ∘ (hsingle 3 (Or.inr rfl)).mpr)
      · exact ((show ¬ (4 : Fin 6) ≤ e6Partner 4 by decide) hi).elim
      · exact ((show ¬ (5 : Fin 6) ≤ e6Partner 5 by decide) hi).elim
    · intro i
      fin_cases i
      · have hrep : FieldLeading S.xi n (torusFieldEntry S b t.val 0) (r (torusOrbit 0)) :=
          hr (torusOrbit 0)
        simpa [torusLeadingFactor] using hrep
      · have hrep : FieldLeading S.xi n (torusFieldEntry S b t.val 1) (r (torusOrbit 1)) :=
          hr (torusOrbit 1)
        simpa [torusLeadingFactor] using hrep
      · have hrep : FieldLeading S.xi n (torusFieldEntry S b t.val 2) (r (torusOrbit 2)) :=
          hr (torusOrbit 2)
        simpa [torusLeadingFactor] using hrep
      · have hrep : FieldLeading S.xi n (torusFieldEntry S b t.val 3) (r (torusOrbit 3)) :=
          hr (torusOrbit 3)
        simpa [torusLeadingFactor] using hrep
      · rw [he]
        change FieldLeading S.xi n (f (T.diagram (q : T.field)) - 1)
          ((torusLeadingFactor S ε n 4 : κ(S.E)) * r (torusOrbit 2))
        simpa [torusLeadingFactor] using hq.2
      · rw [he]
        change FieldLeading S.xi n (f (T.diagram (p : T.field)) - 1)
          ((torusLeadingFactor S ε n 5 : κ(S.E)) * r (torusOrbit 0))
        simpa [torusLeadingFactor] using hp.2
  · intro r hr
    obtain ⟨a, ha⟩ := singleSlot_lift_unit Hk (r (torusOrbit 1))
      (fun h => hr _ (h ∘ (hsingle 1 (Or.inl rfl)).mp))
    obtain ⟨c, hc⟩ := singleSlot_lift_unit Hk (r (torusOrbit 3))
      (fun h => hr _ (h ∘ (hsingle 3 (Or.inr rfl)).mp))
    obtain ⟨p, hp⟩ := singleSlot_lift_unit HK (r (torusOrbit 0))
      (fun h => hr _ (h ∘ (hpair 0 (Or.inl rfl)).mp))
    obtain ⟨q, hq⟩ := singleSlot_lift_unit HK (r (torusOrbit 2))
      (fun h => hr _ (h ∘ (hpair 2 (Or.inr rfl)).mp))
    have Htorus := (RamifiedCongruenceTorusCoordinates.pinnedTorusCoordinates b hspan).2.2.2 R σ T X hdiagram
    obtain ⟨t, ht, _⟩ := Htorus.2.2.2.1 a c p q
    refine ⟨t, fun ⟨i, hi⟩ => ?_⟩
    have he : torusFieldEntry S b t.val i = f (orbitValues T.diagram a c p q i : T.field) - 1 :=
      congrArg (fun z : T.fieldˣ => f (z : T.field) - 1) (ht i)
    fin_cases i
    · exact he.symm ▸ hp
    · exact he.symm ▸ ha
    · exact he.symm ▸ hq
    · exact he.symm ▸ hc
    · exact ((show ¬ (4 : Fin 6) ≤ e6Partner 4 by decide) hi).elim
    · exact ((show ¬ (5 : Fin 6) ≤ e6Partner 5 by decide) hi).elim

private def simpleTorusEntry {B : IntegralAlgebra.{u}} (b : Fin 6 ≃ D.base.support)
    (z : ChartCell X B) (i : Fin 6) : B := (simpleUnit b z.2.1 i : B) - 1

private theorem scaledFieldCell_torus (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (t : X.comparison.chart.chart.torus) (p : ∀ a, X.comparison.chart.parameter a) (i : Fin 6) :
    simpleTorusEntry (X := X) b (scaledFieldCell S (X.comparison.chart.chart.coordinates t p)) i =
      torusFieldEntry S b t.val i := rfl

private theorem fieldLeading_iff_integral (S : ScaledFace T X J x) (n : ℕ) (a : O(S.E)) (r : κ(S.E)) :
    FieldLeading S.xi n (a : S.E) r ↔ IsLeading S n a r := by
  constructor
  · rintro ⟨b, hb, hr⟩
    exact ⟨b, Subtype.ext hb, hr⟩
  · rintro ⟨b, hb, hr⟩
    exact ⟨b, congrArg Subtype.val hb, hr⟩

private theorem fieldLeading_leadingCoefficient (S : ScaledFace T X J x) (n : ℕ)
    (a : O(S.E)) (ha : a ∈ maximalIdeal O(S.E) ^ n) :
    FieldLeading S.xi n (a : S.E) (leadingCoefficient S.xi S.xi_uniformizer.is_generator n ⟨a, ha⟩) := by
  let hπ := S.xi_uniformizer.is_generator
  have hne : S.xi ≠ 0 := fun h => S.xi_uniformizer.ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_pow_iff_factor S.xi hπ n a).mp ha
  exact (fieldLeading_iff_integral S n _ _).mpr
    ⟨c, hc, (leadingCoefficient_eq_of_factor S.xi hπ ⟨a, ha⟩ hne hc).symm⟩

private theorem absoluteLeadingHom_of_chart (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n)
    (g : congruenceSubgroup S n) (w : ChartCell X (localIntegers S.E))
    (he : cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive w =
      S.point (g : parahoric X.comparison J)) (hw : CellDepth S n w) :
    (absoluteLeadingHom S hn g).toAdd = leadingEntries S n w hw := by
  let C := X.comparison.chart
  have h := (markedCellChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates).1 _ ((congruenceCoordinates_spec S hn g).1.trans he.symm)
  subst w
  rfl

private theorem cellValue_of_scaledCoordinates (S : ScaledFace T X J x) (g : parahoric X.comparison J)
    (z : ChartCell X (integralRing T.field)) (w : ChartCell X (localIntegers S.E))
    (hz : cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive z = X.points g)
    (hw : ScaledCoordinates S z w) :
    cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive w = S.point g := by
  let C := X.comparison.chart
  let j := localIntegersInclusion S.E
  have hmap := (markedCellChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates)
  apply changeRing_injective M.toIntegralMarking j (by exact Subtype.val_injective)
  change changeRing j (cellValue M.toIntegralMarking _ C.negative C.positive w) = _
  rw [hmap.2, hw, ← scaleMarkedCell, ← hmap.2, hz]
  exact (S.point_eq g).symm

private theorem congruenceChartParameters (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n)
    (g : congruenceSubgroup S n) (w : ChartCell X (localIntegers S.E))
    (hw : cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive w =
        S.point (g : parahoric X.comparison J)) :
    ∃ (t : X.comparison.chart.chart.torus) (p : ∀ a, X.comparison.chart.parameter a),
      mapCellValues (localIntegersInclusion S.E) w =
        scaledFieldCell S (X.comparison.chart.chart.coordinates t p) := by
  let C := X.comparison.chart
  obtain ⟨z, ⟨hz, w', hw', _⟩, _⟩ := (parahoricPointCongruence S hn (g : _)).mp g.2
  have hg := cellValue_of_scaledCoordinates S (g : _) z w' hz hw'
  have hww := (markedCellChart M.toIntegralMarking C.negative C.positive
    C.negative_enumerates C.positive_enumerates).1 _ (hw.trans hg.symm)
  obtain ⟨t, p, hp⟩ := (C.rational z).mp ⟨g, hz.symm⟩
  refine ⟨t, p, ?_⟩
  rw [hww, hp]
  exact hw'

private theorem integralUnit_of_atDepth {E : Type*} [Field E] [ValuativeRel E] {n : ℕ}
    (hn : 0 < n) (z : Eˣ) (hz : AtDepth n ((z : E) - 1)) :
    ∃ u : O(E)ˣ, (u : O(E)) - 1 ∈ maximalIdeal O(E) ^ n ∧ fieldUnit u = z := by
  obtain ⟨a, ha, hae⟩ := hz
  have hu : IsUnit (1 + a) := by
    apply isUnit_of_mem_nonunits_one_sub_self
    rw [← mem_maximalIdeal, show 1 - (1 + a) = -a by ring]
    exact (maximalIdeal O(E)).neg_mem (Ideal.pow_le_self hn.ne' ha)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_, ?_⟩
  · rwa [hu, add_sub_cancel_left]
  · apply Units.ext
    change ((u : O(E)) : E) = (z : E)
    rw [hu]
    change 1 + (a : E) = (z : E)
    rw [hae]
    ring

set_option maxHeartbeats 600000 in
private theorem integralCell_of_atDepth (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (hspan : D.datum.rootSpan ℤ = ⊤) {n : ℕ} (hn : 0 < n)
    (z : ChartCell X (integralRing S.E))
    (hroot : ∀ j : RootSlot X, AtDepth n (rootCellEntry z j))
    (htorus : ∀ i, AtDepth n (simpleTorusEntry (X := X) b z i)) :
    ∃ w : ChartCell X (localIntegers S.E),
      mapCellValues (localIntegersInclusion S.E) w = z ∧ CellDepth S n w := by
  let O := localIntegers S.E
  let F := integralRing S.E
  have H := RamifiedCongruenceTorusCoordinates.pinnedTorusCoordinates b hspan
  choose q hq hqe using hroot
  choose u hu hue using fun i => integralUnit_of_atDepth hn (simpleUnit b z.2.1 i) (htorus i)
  obtain ⟨t, ht, _⟩ := H.2.1 O u
  have htu : (fieldUnit (E := S.E)).comp t = z.2.1 := by
    obtain ⟨w, _, hw⟩ := H.2.1 F (simpleUnit b z.2.1)
    apply (hw _ ?_).trans (hw _ (fun _ => rfl)).symm
    intro i
    change fieldUnit (simpleUnit b t i) = simpleUnit b z.2.1 i
    rw [ht, hue]
  refine ⟨(fun i => q (.inl i), t, fun i => q (.inr i)), ?_, ?_⟩
  · exact Prod.ext (funext fun i => hqe (.inl i)) <|
      Prod.ext htu (funext fun i => hqe (.inr i))
  · refine ⟨fun i => hq (.inl i), ?_, fun i => hq (.inr i)⟩
    intro χ
    exact H.2.2.1 S.E n hn t (fun i => by rw [ht]; exact hu i) χ.toAdd

private theorem scaledRootEntry_eq (S : ScaledFace T X J x)
    (w : ChartCell X (localIntegers S.E)) (t : X.comparison.chart.chart.torus)
    (p : ∀ a, X.comparison.chart.parameter a)
    (h : mapCellValues (localIntegersInclusion S.E) w = scaledFieldCell S (X.comparison.chart.chart.coordinates t p))
    {a : FoldedRootDirection} (j : RootFiber X a) :
    (rootCellEntry w j.val : S.E) = scaledRootEntry S j (p a) := by
  rw [← scaledFieldCell_root S t p j, ← h]
  rcases j with ⟨i | i, _⟩ <;> rfl

private theorem torusFieldEntry_eq (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (w : ChartCell X (localIntegers S.E)) (t : X.comparison.chart.chart.torus)
    (p : ∀ a, X.comparison.chart.parameter a)
    (h : mapCellValues (localIntegersInclusion S.E) w = scaledFieldCell S (X.comparison.chart.chart.coordinates t p))
    (i : Fin 6) : (simpleTorusEntry (X := X) b w i : S.E) = torusFieldEntry S b t.val i := by
  rw [← scaledFieldCell_torus S b t p i, ← h]
  rfl

private theorem rootLeadingEntry_leading (S : ScaledFace T X J x) {n : ℕ}
    (w : ChartCell X (localIntegers S.E)) (hw : CellDepth S n w) (j : RootSlot X) :
    FieldLeading S.xi n (rootCellEntry w j : S.E) (rootLeadingEntry S (leadingEntries S n w hw) j) := by
  rcases j with i | i
  · exact fieldLeading_leadingCoefficient S n _ (hw.1 i)
  · exact fieldLeading_leadingCoefficient S n _ (hw.2.2 i)

private theorem simpleTorusEntry_leading (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support) {n : ℕ}
    (w : ChartCell X (localIntegers S.E)) (hw : CellDepth S n w) (i : Fin 6) :
    FieldLeading S.xi n (simpleTorusEntry (X := X) b w i : S.E)
      ((leadingEntries S n w hw).2.1 (Multiplicative.ofAdd (D.datum.root (b i).val))) :=
  fieldLeading_leadingCoefficient S n _ (hw.2.1 _)

private abbrev OrbitSlot := FoldedRootDirection ⊕ TorusOrbits

private abbrev SlotActive (S : ScaledFace T X J x) (n : ℕ) : OrbitSlot → Prop
  | .inl a => RootActive S n a
  | .inr a => TorusActive S n a

private theorem slotValue_at_active (S : ScaledFace T X J x) (n : ℕ)
    (v : LayerVectors S n) (i : ActiveSlot S n) : slotValue S n v i.val = v i := by
  unfold slotValue
  split
  next h => exact congrArg v (Subtype.ext h.choose_spec)
  next h => exact (h ⟨i, rfl⟩).elim

private theorem slotValue_at_inactive (S : ScaledFace T X J x) (n : ℕ)
    (v : LayerVectors S n) (i : OrbitSlot) (hi : ¬ SlotActive S n i) : slotValue S n v i = 0 := by
  unfold slotValue
  split
  next h =>
    obtain ⟨j, hj⟩ := h
    exact (hi (hj ▸ j.property)).elim
  next _ => rfl

private theorem slotValue_of_supported (S : ScaledFace T X J x) (n : ℕ)
    (v : OrbitSlot → κ(S.E)) (i : OrbitSlot) (hi : ¬ SlotActive S n i → v i = 0) :
    slotValue S n (fun j => v j.val) i = v i := by
  unfold slotValue
  split
  next h => exact congrArg v h.choose_spec
  next h => exact (hi (fun h' => h ⟨⟨i, h'⟩, rfl⟩)).symm

private def orbitLeadingEntry (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support) {n : ℕ}
    (roots : ∀ a, RootOrbitLayer S n a) (v : AbsoluteLeadingVectors S) : OrbitSlot → κ(S.E)
  | .inl a => rootLeadingEntry S v (roots a).representative.val
  | .inr a => v.2.1 (Multiplicative.ofAdd (D.datum.root (b a.val).val))

private def relativeLeadingHom (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support) {n : ℕ}
    (hn : 0 < n) (roots : ∀ a, RootOrbitLayer S n a) :
    congruenceSubgroup S n →* Multiplicative (LayerVectors S n) :=
  let project : AbsoluteLeadingVectors S →+ LayerVectors S n :=
    { toFun := fun v i => orbitLeadingEntry S b roots v i.val
      map_zero' := by
        funext i
        rcases i with ⟨a | a, _⟩
        · change rootLeadingEntry S 0 (roots a).representative.val = 0
          generalize (roots a).representative.val = j
          rcases j with j | j <;> rfl
        · rfl
      map_add' := fun u v => by
        funext i
        rcases i with ⟨a | a, _⟩
        · change rootLeadingEntry S (u + v) (roots a).representative.val =
            rootLeadingEntry S u (roots a).representative.val + rootLeadingEntry S v (roots a).representative.val
          generalize (roots a).representative.val = j
          rcases j with j | j <;> rfl
        · rfl }
  project.toMultiplicative.comp (absoluteLeadingHom S hn)

private theorem relativeLeadingHom_equivariant (S : ScaledFace T X J x)
    (b : Fin 6 ≃ D.base.support) {n : ℕ} (hn : 0 < n) (roots : ∀ a, RootOrbitLayer S n a)
    (γ' : Gal(k/F)) (g : congruenceSubgroup S n) (i : ActiveSlot S n) :
    ((relativeLeadingHom S b hn roots) ⟨S.action γ' g, congruenceSubgroup_stable S hn γ' g⟩).toAdd i =
      residueAction S γ' (((relativeLeadingHom S b hn roots) g).toAdd i) := by
  change orbitLeadingEntry S b roots ((absoluteLeadingHom S hn)
      ⟨S.action γ' g, congruenceSubgroup_stable S hn γ' g⟩).toAdd i.val =
    residueAction S γ' (orbitLeadingEntry S b roots ((absoluteLeadingHom S hn) g).toAdd i.val)
  rw [absoluteLeadingHom_equivariant S hn γ' g]
  rcases i with ⟨a | a, _⟩
  · simp only [orbitLeadingEntry]
    generalize (roots a).representative.val = j
    rcases j with j | j <;> rfl
  · rfl

private theorem integralChartCongruence (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n)
    (g : parahoric X.comparison J) :
    g ∈ congruenceSubgroup S n ↔
      ∃! w : ChartCell X (localIntegers S.E),
        cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive w = S.point g ∧
          CellDepth S n w :=
  let C := X.comparison.chart
  markedIdentityCongruence M.toIntegralMarking _ _ _ C.negative_enumerates C.positive_enumerates hn _

private theorem cellDepth_of_chart (S : ScaledFace T X J x) {n : ℕ} (hn : 0 < n)
    (g : congruenceSubgroup S n) (w : ChartCell X (localIntegers S.E))
    (he : cellValue M.toIntegralMarking _ X.comparison.chart.negative X.comparison.chart.positive w =
        S.point (g : parahoric X.comparison J)) : CellDepth S n w := by
  let C := X.comparison.chart
  have hz := congruenceCoordinates_spec S hn g
  have h := (markedCellChart M.toIntegralMarking _ _ C.negative_enumerates C.positive_enumerates).1 _
    (hz.1.trans he.symm)
  exact h ▸ hz.2

set_option maxHeartbeats 950000 in
private theorem relativeLeadingHom_comparison (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    {n : ℕ} (hn : 0 < n) (roots : ∀ a, RootOrbitLayer S n a) (torus : TorusOrbitLayer S b n) :
    leadingMapComparison S b n (relativeLeadingHom S b hn roots) := by
  let dir (j : RootSlot X) := A.direction (rootSlotIndex X j)
  let factor (j : RootSlot X) := (roots (dir j)).factor ⟨j, rfl⟩
  have factor_eq (a : FoldedRootDirection) (j : RootFiber X a) :
      factor j.val = (roots a).factor j := by
    rcases j with ⟨j, h⟩
    subst a
    rfl
  refine ⟨fun j => factor (.inl j), fun j => factor (.inr j), torus.factor, ?_,
    torus.factor_representative, ?_⟩
  · intro a
    let rep := (roots a).representative
    have h := rep.property
    have h₁ := (factor_eq a rep).trans (roots a).factor_representative
    rcases he : rep.val with j | j
    · refine Or.inl ⟨j, ?_, ?_⟩
      · change A.direction (rootSlotIndex X (.inl j)) = a
        rwa [← he]
      · change factor (.inl j) = 1
        rwa [← he]
    · refine Or.inr ⟨j, ?_, ?_⟩
      · change A.direction (rootSlotIndex X (.inr j)) = a
        rwa [← he]
      · change factor (.inr j) = 1
        rwa [← he]
  · intro g w he
    let hw := cellDepth_of_chart S hn g w he
    let v := leadingEntries S n w hw
    obtain ⟨t, p, hp⟩ := congruenceChartParameters S hn g w he
    have hroot (a : FoldedRootDirection) :=
      let rep := (roots a).representative
      (roots a).compare (p a) (rootLeadingEntry S v rep.val)
        (scaledRootEntry_eq S w t p hp rep ▸ rootLeadingEntry_leading S w hw rep.val)
    let r (a : TorusOrbits) := v.2.1 (Multiplicative.ofAdd (D.datum.root (b a.val).val))
    have htorus := torus.compare t r (fun a =>
      torusFieldEntry_eq S b w t p hp a.val ▸ simpleTorusEntry_leading S b w hw a.val)
    have hr (i : OrbitSlot) :
        slotValue S n ((relativeLeadingHom S b hn roots g).toAdd) i = orbitLeadingEntry S b roots v i := by
      change slotValue S n (fun j => orbitLeadingEntry S b roots ((absoluteLeadingHom S hn g).toAdd) j.val) i = _
      rw [absoluteLeadingHom_of_chart S hn g w he hw]
      apply slotValue_of_supported
      rcases i with a | a
      · exact (hroot a).1
      · exact htorus.1 a
    have hroot' (j : RootSlot X) : IsLeading S n (rootCellEntry w j)
        ((factor j : κ(S.E)) * slotValue S n (relativeLeadingHom S b hn roots g).toAdd (.inl (dir j))) := by
      rw [hr]
      apply (fieldLeading_iff_integral S n _ _).mp
      let j' : RootFiber X (dir j) := ⟨j, rfl⟩
      rw [scaledRootEntry_eq S w t p hp j']
      exact (hroot (dir j)).2 j'
    refine ⟨fun j => hroot' (.inl j), fun j => hroot' (.inr j), ?_⟩
    intro i
    rw [hr]
    apply (fieldLeading_iff_integral S n _ _).mp
    change FieldLeading S.xi n (simpleTorusEntry (X := X) b w i : S.E) _
    rw [torusFieldEntry_eq S b w t p hp i]
    exact htorus.2 i

set_option maxHeartbeats 1200000 in
private theorem relativeLeadingHom_surjective (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (hspan : D.datum.rootSpan ℤ = ⊤) {n : ℕ} (hn : 0 < n)
    (roots : ∀ a, RootOrbitLayer S n a) (torus : TorusOrbitLayer S b n)
    (Y : Building X.comparison) (t₀ : Weights (A.roots.SimpleWall A.basepoint))
    (hx : rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t₀) :
    Function.Surjective (relativeLeadingHom S b hn roots) := by
  intro v
  let C := X.comparison.chart
  let r := slotValue S n v.toAdd
  have hz (i : OrbitSlot) (hi : ¬ SlotActive S n i) : r i = 0 := slotValue_at_inactive S n _ i hi
  choose p hp using fun a => (roots a).lift (r (.inl a)) (hz (.inl a))
  obtain ⟨t, ht⟩ := torus.lift (fun a => r (.inr a)) (fun a => hz (.inr a))
  let z := C.chart.coordinates t p
  let z' := scaledFieldCell S z
  have hroot (j : RootSlot X) : AtDepth n (rootCellEntry z' j) := by
    let a := A.direction (rootSlotIndex X j)
    let j' : RootFiber X a := ⟨j, rfl⟩
    rw [show rootCellEntry z' j = scaledRootEntry S j' (p a) from scaledFieldCell_root S t p j']
    exact fieldLeading_atDepth S.xi_uniformizer (((roots a).compare (p a) (r (.inl a)) (hp a)).2 j')
  have htorus (i : Fin 6) : AtDepth n (simpleTorusEntry (X := X) b z' i) := by
    rw [show simpleTorusEntry (X := X) b z' i = torusFieldEntry S b t.val i from scaledFieldCell_torus S b t p i]
    exact fieldLeading_atDepth S.xi_uniformizer ((torus.compare t (fun a => r (.inr a)) ht).2 i)
  obtain ⟨w, he, hw⟩ := integralCell_of_atDepth S b hspan hn z' hroot htorus
  obtain ⟨g, hg⟩ := (C.rational z).mpr ⟨t, p, rfl⟩
  obtain ⟨hgP, hgN⟩ := (parahoricChartCongruence S Y t₀ hx hn g).mpr
    ⟨z, ⟨hg.symm, w, he, hw⟩, fun z₁ hz₁ => (markedCellChart M.toIntegralMarking _ _
      C.negative_enumerates C.positive_enumerates).1 _ (hz₁.1.trans hg)⟩
  let g' : congruenceSubgroup S n := ⟨⟨g, hgP⟩, hgN⟩
  have hwval := cellValue_of_scaledCoordinates S (g' : _) z w hg.symm he
  refine ⟨g', ?_⟩
  change (fun i : ActiveSlot S n => orbitLeadingEntry S b roots ((absoluteLeadingHom S hn g').toAdd) i.val) = v.toAdd
  rw [absoluteLeadingHom_of_chart S hn g' w hwval hw]
  funext i
  rcases i with ⟨a | a, ha⟩
  · let rep := (roots a).representative
    have h := rootLeadingEntry_leading S w hw rep.val
    rw [scaledRootEntry_eq S w t p he rep] at h
    exact (fieldLeading_unique S.xi_uniformizer.ne_zero h (hp a)).trans
      (slotValue_at_active S n v.toAdd ⟨.inl a, ha⟩)
  · have h := simpleTorusEntry_leading S b w hw a.val
    rw [torusFieldEntry_eq S b w t p he a.val] at h
    exact (fieldLeading_unique S.xi_uniformizer.ne_zero h (ht a)).trans
      (slotValue_at_active S n v.toAdd ⟨.inr a, ha⟩)

private theorem mem_next_of_leading_zero (S : ScaledFace T X J x) {n : ℕ}
    (z : O(S.E)) (hz : z ∈ maximalIdeal O(S.E) ^ n) (h : IsLeading S n z 0) :
    z ∈ maximalIdeal O(S.E) ^ (n + 1) := by
  let hπ := S.xi_uniformizer.is_generator
  have hne : S.xi ≠ 0 := fun e => S.xi_uniformizer.ne_zero (congrArg Subtype.val e)
  apply (leadingCoefficient_zero_iff S.xi hπ ⟨z, hz⟩ hne).mp
  exact fieldLeading_unique S.xi_uniformizer.ne_zero (fieldLeading_leadingCoefficient S n z hz)
    ((fieldLeading_iff_integral S n _ _).mpr h)

set_option maxHeartbeats 800000 in
private theorem relativeLeadingHom_kernel (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (hspan : D.datum.rootSpan ℤ = ⊤) {n : ℕ} (hn : 0 < n)
    (roots : ∀ a, RootOrbitLayer S n a) (torus : TorusOrbitLayer S b n) (g : congruenceSubgroup S n) :
    relativeLeadingHom S b hn roots g = 1 ↔ (g : parahoric X.comparison J) ∈ congruenceSubgroup S (n + 1) := by
  constructor
  · intro hz
    let w := congruenceCoordinates S hn g
    obtain ⟨he, hw⟩ := congruenceCoordinates_spec S hn g
    have hzero (i : OrbitSlot) : slotValue S n (relativeLeadingHom S b hn roots g).toAdd i = 0 := by
      rw [hz]
      unfold slotValue
      split <;> rfl
    obtain ⟨_, _, _, _, _, hc⟩ := relativeLeadingHom_comparison S b hn roots torus
    obtain ⟨hneg, hpos, htor⟩ := hc g w he
    have ht (i : Fin 6) : simpleTorusEntry (X := X) b w i ∈ maximalIdeal O(S.E) ^ (n + 1) := by
      have h := htor i
      rw [hzero, mul_zero] at h
      exact mem_next_of_leading_zero S _ (hw.2.1 _) h
    have hnext : CellDepth S (n + 1) w := by
      refine ⟨fun i => mem_next_of_leading_zero S _ (hw.1 i) (by simpa only [hzero, mul_zero] using hneg i),
        ?_, fun i => mem_next_of_leading_zero S _ (hw.2.2 i) (by simpa only [hzero, mul_zero] using hpos i)⟩
      intro χ
      exact (RamifiedCongruenceTorusCoordinates.pinnedTorusCoordinates b hspan).2.2.1 S.E
        (n + 1) (Nat.succ_pos n) w.2.1 ht χ.toAdd
    apply (integralChartCongruence S (Nat.succ_pos n) (g : _)).mpr
    let C := X.comparison.chart
    exact ⟨w, ⟨he, hnext⟩, fun z hz => (markedCellChart M.toIntegralMarking _ _
      C.negative_enumerates C.positive_enumerates).1 _ (hz.1.trans he.symm)⟩
  · intro h
    unfold relativeLeadingHom
    rw [MonoidHom.comp_apply, (absoluteLeadingHom_ker S hn g).mpr h, map_one]

private abbrev RelativeLayerAt (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support) (n : ℕ) :=
  ∃ (stable : ∀ g (h : congruenceSubgroup S n), S.action g h ∈ congruenceSubgroup S n)
    (red : congruenceSubgroup S n →* Multiplicative (LayerVectors S n)),
    leadingMapComparison S b n red ∧ Function.Surjective red ∧
    (∀ h, red h = 1 ↔ (h : parahoric X.comparison J) ∈ congruenceSubgroup S (n + 1)) ∧
    (∀ g (h : congruenceSubgroup S n) i, (red ⟨S.action g h, stable g h⟩).toAdd i =
      residueAction S g ((red h).toAdd i)) ∧
    ∃ e : (congruenceSubgroup S n ⧸ red.ker) ≃* Multiplicative (LayerVectors S n),
      ∀ h, e (QuotientGroup.mk h) = red h

private theorem relativeLayer (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support)
    (hspan : D.datum.rootSpan ℤ = ⊤)
    (hdiagram : ∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i))
    (Y : Building X.comparison) (t : Weights (A.roots.SimpleWall A.basepoint))
    (hx : rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t)
    {ε : O(T.field)ˣ} {n : ℕ} (hn : 0 < n) (H : SlotCoefficients S ε n) : RelativeLayerAt S b n := by
  let roots (a : FoldedRootDirection) := Classical.choice (rootOrbitLayer_exists S H a)
  let torus := torusOrbitLayer S b hspan hdiagram H
  let red := relativeLeadingHom S b hn roots
  have hsurj : Function.Surjective red := relativeLeadingHom_surjective S b hspan hn roots torus Y t hx
  refine ⟨congruenceSubgroup_stable S hn, red, relativeLeadingHom_comparison S b hn roots torus, hsurj,
    relativeLeadingHom_kernel S b hspan hn roots torus, relativeLeadingHom_equivariant S b hn roots, ?_⟩
  exact ⟨QuotientGroup.quotientKerEquivOfSurjective red hsurj, fun _ => rfl⟩

private theorem closedCongruenceSubgroups (S : ScaledFace T X J x)
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ M.group.X) :
    letI := TopologicalSpace.induced X.points (markedPointTopology B iso T.field)
    ∀ n, IsClosed (congruenceSubgroup S n : Set (parahoric X.comparison J)) := by
  have hf : Continuous (algebraMap T.field S.E) :=
    RamifiedCongruencePointTopology.markedScalarContinuity.2 _ S.d S.d_pos (auxiliaryValuation S)
  exact RamifiedCongruencePointTopology.closedParahoricReductionKernel X.comparison J B iso
    S.xi S.xi_uniformizer (algebraMap T.field S.E) hf _ S.point S.point_eq

set_option maxHeartbeats 1000000 in
private theorem compactCocycleCorrection [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [ValuativeExtension F k]
    (S : ScaledFace T X J x) (b : Fin 6 ≃ D.base.support) (Y : Building X.comparison)
    (hJ : J ≠ Set.univ) (hX : X.Coefficients T)
    (galResidue : Gal(k/F) ≃* Gal(κ(k)/κ(F))) (hres : ResidueComparison S galResidue)
    (layers : ∀ n, 0 < n → RelativeLayerAt S b n)
    (a : Gal(k/F) → parahoric X.comparison J)
    (ha : ∀ g h, a (g * h) = a g * S.action g (a h)) (hfirst : ∀ g, a g ∈ congruenceSubgroup S 1) :
    ∃ h : congruenceSubgroup S 1, ∀ g,
      a g = (h : parahoric X.comparison J) * (S.action g h)⁻¹ := by
  obtain ⟨i, j, _, _, hresidue⟩ := hres
  let e := i.trans j
  obtain ⟨B, _, ⟨iso⟩⟩ := RamifiedCongruencePointTopology.finiteTypePresentation M.toIntegralMarking
  letI : TopologicalSpace (GroupPoints R.descent.group.val (CommAlgCat.of F k)) :=
    TopologicalSpace.induced X.points (markedPointTopology B iso T.field)
  have htop := RamifiedCongruencePointTopology.compactParahoric Y J hJ B iso
  letI : IsTopologicalGroup (parahoric X.comparison J) := htop.2.2.1
  letI : CompactSpace (parahoric X.comparison J) := htop.2.2.2
  letI : Finite κ(k) := inferInstanceAs (Finite (IsLocalRing.ResidueField ((valuation k).integer)))
  letI : FiniteDimensional κ(F) κ(k) := Module.Finite.of_finite
  have hsep (g : parahoric X.comparison J)
      (hg : ∀ n, g ∈ congruenceSubgroup S (n + 1)) : g = 1 := by
    apply congruenceSubgroup_separated S g
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact hg m
  apply compactSemilinearCorrection S.action (continuous_parahoricCoefficient S hX B iso) galResidue
    (fun n => congruenceSubgroup S (n + 1))
    (fun _ _ h => congruenceSubgroup_antitone S (Nat.succ_le_succ h))
    (fun n => closedCongruenceSubgroups S B iso (n + 1)) hsep _ a ha hfirst
  intro n
  obtain ⟨stable, red, _, hsurj, hker, hequiv, _⟩ := layers (n + 1) (Nat.succ_pos n)
  let e' : Multiplicative (LayerVectors S (n + 1)) ≃* Multiplicative (ActiveSlot S (n + 1) → κ(k)) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight (fun _ => e.symm.toAddEquiv))
  let red' := e'.toMonoidHom.comp red
  refine ⟨ActiveSlot S (n + 1), stable, red', e'.surjective.comp hsurj, ?_, ?_⟩
  · intro g
    change e' (red g) = 1 ↔ _
    rw [← e'.map_one, e'.injective.eq_iff, hker]
  · intro τ g a'
    let r := (red g).toAdd a'
    change e.symm ((red ⟨S.action τ g, stable τ g⟩).toAdd a') = galResidue τ (e.symm r)
    rw [hequiv]
    have h := hresidue τ (e.symm r)
    change residueAction S τ (e (e.symm r)) = e (galResidue τ (e.symm r)) at h
    rw [e.apply_symm_apply] at h
    change e.symm (residueAction S τ r) = _
    rw [h, e.symm_apply_apply]

private def coefficientScaling (S : ScaledFace T X J x) : AuxiliaryScaling T where
  E := S.E
  field := S.field
  algebra := S.algebra
  valuation := S.valuation
  topology := S.topology
  localField := S.localField
  finite := S.finite
  extension := S.extension
  d := S.d
  d_pos := S.d_pos
  uniformizer := S.uniformizer
  uniformizer_value := S.uniformizer_value
  xi := S.xi
  xi_uniformizer := S.xi_uniformizer
  xi_power := S.xi_power
  unchanged_residue := S.unchanged_residue
  coefficient := S.coefficient
  coefficient_extends := S.coefficient_extends
  coefficient_fixes_xi := S.coefficient_fixes_xi
  integralCoefficient := S.integralCoefficient
  integralCoefficient_eq := S.integralCoefficient_eq

set_option maxHeartbeats 900000 in
/-- Successive congruence quotients and cocycle correction for the scaled
adjoint parahoric over the given finite unramified coefficient field. -/
theorem ramifiedFaceCongruenceLayers : RamifiedFaceCongruenceLayers.{u} := by
  intro F L k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hUnram σ hdegree hσ hram D M R b _ hspan hdiagram T A X hX Y J hJ x t _ _ hx S galResidue hgal
  obtain ⟨_, _, _, _, hres, ε, _, hslots⟩ :=
    RamifiedCongruenceCoefficientDepths.ramifiedCoefficientDepths F L k hUnram σ hdegree hσ hram
      R T A X (coefficientScaling S) galResidue hgal
  have hres' : ResidueComparison S galResidue := hres
  have hlayers (n : ℕ) (hn : 0 < n) : RelativeLayerAt S b n :=
    relativeLayer S b hspan hdiagram Y t hx hn (hslots n hn)
  refine ⟨?_, hres'⟩
  refine ⟨fun _ hn g => parahoricChartCongruence S Y t hx hn g,
    fun _ hn g => integralChartCongruence S hn g, congruenceSubgroup_antitone S,
    congruenceSubgroup_separated S, ?_, hlayers,
    compactCocycleCorrection S b Y hJ hX galResidue hres' hlayers⟩
  intro B _ iso
  exact ⟨(RamifiedCongruencePointTopology.compactParahoric Y J hJ B iso).2.1,
    closedCongruenceSubgroups S B iso⟩

end CoordinateLayers


end

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceCongruence
