import Specs.LinearAlgebraicGroups.Arithmetic.RationalContraction
import LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
import Mathlib.RingTheory.GradedAlgebra.AlgHom
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.Algebra.MonoidAlgebra.Grading
import LinearAlgebraicGroups.Flag.SmoothOrbit
import LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Batteries.Tactic.OpenPrivate

open scoped DirectSum

universe u

namespace LinearAlgebraicGroups.Arithmetic.RationalContraction

noncomputable section

section GradedLifting

variable {k A B C : Type u} [Field k]
  [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]

private theorem graded_induction {T : Type u} [CommRing T] [Algebra k T]
    (grading : ℤ → Submodule k T) [GradedAlgebra grading]
    (P : T → Prop) (x : T) (homogeneous : ∀ i t, t ∈ grading i → P t)
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  have h := (DirectSum.Decomposition.isInternal grading).submodule_iSup_eq_top
  exact Submodule.iSup_induction (motive := P) grading
    (h ▸ Submodule.mem_top (R := k) (M := T) (x := x)) homogeneous zero add

private theorem proj_of_mem {T : Type u} [CommRing T] [Algebra k T]
    (grading : ℤ → Submodule k T) [GradedAlgebra grading]
    {i : ℤ} {x : T} (hx : x ∈ grading i) :
    GradedAlgebra.proj grading i x = x :=
  DirectSum.decompose_of_mem_same grading hx

private theorem proj_mul {T : Type u} [CommRing T] [Algebra k T]
    (grading : ℤ → Submodule k T) [GradedAlgebra grading]
    {i j : ℤ} {x y : T} (hx : x ∈ grading i) (hy : y ∈ grading j) :
    GradedAlgebra.proj grading (i + j) (x * y) = x * y :=
  proj_of_mem _ (SetLike.GradedMul.mul_mem hx hy)

/-- Keep the part of a linear map that preserves the degree. -/
private def homogeneousPart
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB] (g : A →ₗ[k] B) :
    A →ₗ[k] B :=
  (DirectSum.toModule k ℤ B
    (fun i ↦ GradedAlgebra.proj gradingB i ∘ₗ g ∘ₗ (gradingA i).subtype)).comp
    (DirectSum.decomposeLinearEquiv gradingA).toLinearMap

private theorem homogeneousPart_apply
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB] (g : A →ₗ[k] B)
    {i : ℤ} {a : A} (ha : a ∈ gradingA i) :
    homogeneousPart gradingA gradingB g a = GradedAlgebra.proj gradingB i (g a) := by
  let x : gradingA i := ⟨a, ha⟩
  change homogeneousPart gradingA gradingB g (x : A) = _
  simp only [homogeneousPart, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof, Submodule.subtype_apply]
  rfl

/-- The homogeneous part of an algebra lift remains multiplicative when
the error ideal of the quotient has square zero. -/
private def homogeneousLift
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB]
    (gradingC : ℤ → Submodule k C) [GradedAlgebra gradingC]
    (q : B →ₐ[k] C) (hq : RingHom.ker q.toRingHom ^ 2 = ⊥)
    (q_proj : ∀ i b, q (GradedAlgebra.proj gradingB i b) =
      GradedAlgebra.proj gradingC i (q b))
    (f : A →ₐ[k] C) (f_graded : ∀ i a, a ∈ gradingA i → f a ∈ gradingC i)
    (g : A →ₐ[k] B) (hg : q.comp g = f) :
    A →ₐ[k] B := by
  let L := homogeneousPart gradingA gradingB g.toLinearMap
  have L_apply {i : ℤ} {a : A} (ha : a ∈ gradingA i) :
      L a = GradedAlgebra.proj gradingB i (g a) :=
    homogeneousPart_apply gradingA gradingB g.toLinearMap ha
  have projected {i : ℤ} {a : A} (ha : a ∈ gradingA i) :
      q (g a - GradedAlgebra.proj gradingB i (g a)) = 0 := by
    have he : q (g a) = f a := DFunLike.congr_fun hg a
    rw [map_sub, q_proj, he, proj_of_mem _ (f_graded i a ha), sub_self]
  have mul_homogeneous {i j : ℤ} {a b : A} (ha : a ∈ gradingA i) (hb : b ∈ gradingA j) :
      L (a * b) = L a * L b := by
    rw [L_apply (SetLike.GradedMul.mul_mem ha hb), L_apply ha, L_apply hb, map_mul]
    let a' := GradedAlgebra.proj gradingB i (g a)
    let b' := GradedAlgebra.proj gradingB j (g b)
    let da := g a - a'
    let db := g b - b'
    have ha' : a' ∈ gradingB i := (DirectSum.decompose gradingB (g a) i).property
    have hb' : b' ∈ gradingB j := (DirectSum.decompose gradingB (g b) j).property
    have hda : GradedAlgebra.proj gradingB i da = 0 := by
      simp [da, a']
    have hdb : GradedAlgebra.proj gradingB j db = 0 := by
      simp [db, b']
    have hd : da * db = 0 := by
      have h := Ideal.mul_mem_mul (I := RingHom.ker q.toRingHom)
        (J := RingHom.ker q.toRingHom)
        (RingHom.mem_ker.mpr (projected ha)) (RingHom.mem_ker.mpr (projected hb))
      simpa only [← pow_two, hq, Ideal.mem_bot] using h
    have hleft : GradedAlgebra.proj gradingB (i + j) (a' * db) = 0 := by
      rw [GradedAlgebra.proj_apply, DirectSum.coe_decompose_mul_add_of_left_mem _ ha']
      change a' * GradedAlgebra.proj gradingB j db = 0
      rw [hdb, mul_zero]
    have hright : GradedAlgebra.proj gradingB (i + j) (da * b') = 0 := by
      rw [GradedAlgebra.proj_apply, DirectSum.coe_decompose_mul_add_of_right_mem _ hb']
      change GradedAlgebra.proj gradingB i da * b' = 0
      rw [hda, zero_mul]
    change GradedAlgebra.proj gradingB (i + j) (g a * g b) = a' * b'
    have ea : g a = a' + da := by dsimp [da]; abel
    have eb : g b = b' + db := by dsimp [db]; abel
    rw [ea, eb, add_mul, mul_add, mul_add, hd]
    simp only [map_add, proj_mul _ ha' hb', hleft, hright, add_zero]
  refine
    { toFun := L
      map_zero' := map_zero L
      map_add' := map_add L
      map_one' := ?_
      map_mul' := ?_
      commutes' := ?_ }
  · rw [L_apply (SetLike.GradedOne.one_mem (A := gradingA)), map_one,
      proj_of_mem _ (SetLike.GradedOne.one_mem (A := gradingB))]
  · intro x y
    refine graded_induction gradingA (fun a ↦ ∀ b, L (a * b) = L a * L b) x
      ?_ (by simp) ?_ y
    · intro i a ha b
      refine graded_induction gradingA (fun b ↦ L (a * b) = L a * L b) b
        (fun _ _ hb ↦ mul_homogeneous ha hb) (by simp) ?_
      intro b c hb hc
      simp only [mul_add, map_add, hb, hc]
    · intro a b ha hb c
      simp only [add_mul, map_add, ha, hb]
  · intro c
    rw [L_apply (SetLike.algebraMap_mem_graded gradingA c), AlgHom.commutes,
      proj_of_mem _ (SetLike.algebraMap_mem_graded gradingB c)]

private theorem homogeneousLift_apply
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB]
    (gradingC : ℤ → Submodule k C) [GradedAlgebra gradingC]
    (q : B →ₐ[k] C) (hq) (q_proj)
    (f : A →ₐ[k] C) (f_graded) (g : A →ₐ[k] B) (hg)
    {i : ℤ} {a : A} (ha : a ∈ gradingA i) :
    homogeneousLift gradingA gradingB gradingC q hq q_proj f f_graded g hg a =
      GradedAlgebra.proj gradingB i (g a) := by
  exact homogeneousPart_apply gradingA gradingB g.toLinearMap ha

private theorem homogeneousLift_spec
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB]
    (gradingC : ℤ → Submodule k C) [GradedAlgebra gradingC]
    (q : B →ₐ[k] C) (hq) (q_proj)
    (f : A →ₐ[k] C) (f_graded) (g : A →ₐ[k] B) (hg) :
    let lift := homogeneousLift gradingA gradingB gradingC q hq q_proj f f_graded g hg
    (q.comp lift = f) ∧ (∀ i a, a ∈ gradingA i → lift a ∈ gradingB i) := by
  dsimp only
  constructor
  · ext a
    refine graded_induction gradingA
      (fun a ↦ q (homogeneousLift gradingA gradingB gradingC q hq q_proj f f_graded g hg a) =
        f a) a ?_ (by simp) ?_
    · intro i b hb
      have he : q (g b) = f b := DFunLike.congr_fun hg b
      rw [homogeneousLift_apply _ _ _ q hq q_proj f f_graded g hg hb,
        q_proj, he, proj_of_mem _ (f_graded i b hb)]
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · intro i a ha
    rw [homogeneousLift_apply _ _ _ q hq q_proj f f_graded g hg ha]
    exact (DirectSum.decompose gradingB (g a) i).property

private abbrev quotientGrading
    (grading : ℤ → Submodule k A) (J : Ideal A) (i : ℤ) : Submodule k (A ⧸ J) :=
  (grading i).map (Ideal.Quotient.mkₐ k J).toLinearMap

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient by an ideal stable under projection inherits the grading. -/
@[instance_reducible] private def gradedQuotient
    (grading : ℤ → Submodule k A) [GradedAlgebra grading] (J : Ideal A)
    (stable : ∀ i a, a ∈ J → GradedAlgebra.proj grading i a ∈ J) :
    GradedAlgebra (quotientGrading grading J) := by
  let q := Ideal.Quotient.mkₐ k J
  let mapComponent (i : ℤ) : grading i →ₗ[k] quotientGrading grading J i :=
    (q.toLinearMap.comp (grading i).subtype).codRestrict _ fun x ↦
      Submodule.mem_map_of_mem x.property
  let H := DirectSum.lmap mapComponent ∘ₗ (DirectSum.decomposeLinearEquiv grading).toLinearMap
  have H_zero (a : A) (ha : a ∈ J) : H a = 0 := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    change q (GradedAlgebra.proj grading i a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (stable i a ha)
  let Lfun (x : A ⧸ J) := Quotient.liftOn' x (fun a ↦ H a) (fun a b h ↦ by
    have hmem : a - b ∈ J := Ideal.Quotient.eq.mp (Quotient.sound' h)
    have he := map_add H (a - b) b
    simpa only [sub_add_cancel, H_zero _ hmem, zero_add] using he)
  let L : (A ⧸ J) →+ ⨁ i, quotientGrading grading J i :=
    { toFun := Lfun
      map_zero' := map_zero H
      map_add' := fun x y ↦ Quotient.inductionOn₂' x y (map_add H) }
  have onHomogeneous {i : ℤ} (x : grading i) :
      L (q x) = DirectSum.lof k ℤ (fun i ↦ quotientGrading grading J i) i (mapComponent i x) := by
    change H x = _
    simp [H]
  letI : SetLike.GradedMonoid (quotientGrading grading J) := {
    one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one q⟩
    mul_mem := by
      rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul q a b⟩ }
  refine { (inferInstance : SetLike.GradedMonoid (quotientGrading grading J)) with
    toDecomposition := DirectSum.Decomposition.ofAddHom (quotientGrading grading J) L ?_ ?_ }
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change DirectSum.coeAddMonoidHom (quotientGrading grading J) (L (q a)) = q a
    refine graded_induction grading
      (fun a ↦ DirectSum.coeAddMonoidHom (quotientGrading grading J) (L (q a)) = q a)
      a ?_ (by simp) ?_
    · intro i a ha
      rw [onHomogeneous (⟨a, ha⟩ : grading i)]
      rw [DirectSum.lof_eq_of, DirectSum.coeAddMonoidHom_of]
      rfl
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · apply DirectSum.addHom_ext
    intro i x
    obtain ⟨a, ha, he⟩ := x.property
    have e : mapComponent i ⟨a, ha⟩ = x := Subtype.ext he
    have h : (x : A ⧸ J) = q a := he.symm
    change L (DirectSum.coeAddMonoidHom _ (DirectSum.of _ i x)) = DirectSum.of _ i x
    rw [DirectSum.coeAddMonoidHom_of, h, onHomogeneous (⟨a, ha⟩ : grading i), e]
    rfl

private theorem exists_relative_lift {D : Type u} [CommRing D] [Algebra k D]
    (α : A →ₐ[k] B) (hα : α.toRingHom.FormallySmooth)
    (q : C →ₐ[k] D) (hq : Function.Surjective q)
    (hnil : IsNilpotent (RingHom.ker q.toRingHom))
    (f : B →ₐ[k] D) (s : A →ₐ[k] C) (compat : f.comp α = q.comp s) :
    ∃ g : B →ₐ[k] C, q.comp g = f ∧ g.comp α = s := by
  let : Algebra A B := α.toRingHom.toAlgebra
  let : Algebra A C := s.toRingHom.toAlgebra
  let : Algebra A D := (q.comp s).toRingHom.toAlgebra
  let : Algebra.FormallySmooth A B := hα
  let q' : C →ₐ[A] D := ⟨q.toRingHom, fun _ ↦ rfl⟩
  let f' : B →ₐ[A] D := ⟨f.toRingHom, DFunLike.congr_fun compat⟩
  let g' := Algebra.FormallySmooth.liftOfSurjective f' q' hq hnil
  let g : B →ₐ[k] C := ⟨g'.toRingHom, fun r ↦ by
    change g' (algebraMap k B r) = algebraMap k C r
    rw [← α.commutes r]
    exact (g'.commutes (algebraMap k A r)).trans (s.commutes r)⟩
  refine ⟨g, ?_, ?_⟩
  · ext b
    exact Algebra.FormallySmooth.liftOfSurjective_apply f' q' hq hnil b
  · ext a
    exact g'.commutes a

private theorem exists_graded_relative_lift {D : Type u} [CommRing D] [Algebra k D]
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB]
    (gradingC : ℤ → Submodule k C) [GradedAlgebra gradingC]
    (gradingD : ℤ → Submodule k D) [GradedAlgebra gradingD]
    (α : A →ₐ[k] B) (hα : α.toRingHom.FormallySmooth)
    (hαg : ∀ i a, a ∈ gradingA i → α a ∈ gradingB i)
    (q : C →ₐ[k] D) (hq : Function.Surjective q) (hnil : RingHom.ker q.toRingHom ^ 2 = ⊥)
    (hqg : ∀ i c, c ∈ gradingC i → q c ∈ gradingD i)
    (f : B →ₐ[k] D) (hfg : ∀ i b, b ∈ gradingB i → f b ∈ gradingD i)
    (s : A →ₐ[k] C) (hsg : ∀ i a, a ∈ gradingA i → s a ∈ gradingC i)
    (compat : f.comp α = q.comp s) :
    ∃ (g : B →ₐ[k] C), q.comp g = f ∧ g.comp α = s ∧
      (∀ i b, b ∈ gradingB i → g b ∈ gradingC i) := by
  obtain ⟨g, hqg', hgs⟩ := exists_relative_lift α hα q hq ⟨2, hnil⟩ f s compat
  let q₀ : gradingC →+*ᵍ gradingD := ⟨q.toRingHom, fun h ↦ hqg _ _ h⟩
  have hproj i c : q (GradedAlgebra.proj gradingC i c) =
      GradedAlgebra.proj gradingD i (q c) :=
    q₀.map_directSumDecompose
  let g₀ := homogeneousLift gradingB gradingC gradingD q hnil hproj f hfg g hqg'
  obtain ⟨hred, hgrade⟩ := homogeneousLift_spec gradingB gradingC gradingD
    q hnil hproj f hfg g hqg'
  refine ⟨g₀, hred, ?_, hgrade⟩
  ext a
  change g₀ (α a) = s a
  refine graded_induction gradingA (fun a ↦ g₀ (α a) = s a) a ?_ (by simp) ?_
  · intro i b hb
    have e : g (α b) = s b := DFunLike.congr_fun hgs b
    rw [show g₀ (α b) = _ from homogeneousLift_apply _ _ _ q hnil hproj
      f hfg g hqg' (hαg i b hb), e, proj_of_mem _ (hsg i b hb)]
  · intro b c hb hc
    simp only [map_add, hb, hc]

private theorem ker_quotient_factor {S : Type u} [CommRing S] [Algebra k S]
    {I J : Ideal S} (h : I ≤ J) :
    RingHom.ker (Ideal.Quotient.factorₐ k h).toRingHom =
      J.map (Ideal.Quotient.mk I) := by
  ext r
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [RingHom.mem_ker, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  change Ideal.Quotient.mk J a = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · exact fun ha ↦ ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, he⟩
    have hd : b - a ∈ I := Ideal.Quotient.eq.mp he
    simpa using J.sub_mem hb (h hd)

private theorem square_zero_quotient_factor {S : Type u} [CommRing S] [Algebra k S]
    (I : Ideal S) {n : ℕ} (hn : 1 ≤ n) :
    RingHom.ker (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (I := I) n.le_succ)).toRingHom ^
      2 = ⊥ := by
  rw [ker_quotient_factor, ← Ideal.map_pow, ← pow_mul]
  exact eq_bot_mono (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)))
    (Ideal.map_quotient_self _)

/-- A coherent graded lift through all powers of a homogeneous ideal gives a
lift to the ring itself when each individual degree stabilizes. -/
private theorem exists_graded_lift_of_powers {S : Type u} [CommRing S] [Algebra k S]
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB]
    (gradingS : ℤ → Submodule k S) [GradedAlgebra gradingS]
    (I : Ideal S)
    (stable : ∀ n i s, s ∈ I ^ n → GradedAlgebra.proj gradingS i s ∈ I ^ n)
    (bounded : ∀ i, ∃ n, ∀ s ∈ gradingS i, s ∈ I ^ n → s = 0)
    (α : A →ₐ[k] B) (hα : α.toRingHom.FormallySmooth)
    (hαg : ∀ i a, a ∈ gradingA i → α a ∈ gradingB i)
    (f : A →ₐ[k] S) (hfg : ∀ i a, a ∈ gradingA i → f a ∈ gradingS i)
    (e : B →ₐ[k] (S ⧸ I ^ 1))
    (he : e.comp α = (Ideal.Quotient.mkₐ k (I ^ 1)).comp f)
    (heg : ∀ i b, b ∈ gradingB i → e b ∈ quotientGrading gradingS (I ^ 1) i) :
    ∃ g : B →ₐ[k] S, g.comp α = f ∧ (Ideal.Quotient.mkₐ k (I ^ 1)).comp g = e ∧
      (∀ i b, b ∈ gradingB i → g b ∈ gradingS i) := by
  classical
  let gradingQ (n : ℕ) := quotientGrading gradingS (I ^ n)
  let (n : ℕ) : GradedAlgebra (gradingQ n) := gradedQuotient gradingS (I ^ n) (stable n)
  let mk (n : ℕ) := Ideal.Quotient.mkₐ k (I ^ n)
  let lower {m n : ℕ} (h : m ≤ n) := Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (I := I) h)
  have mk_lower {m n : ℕ} (h : m ≤ n) (s : S) : lower h (mk n s) = mk m s := rfl
  have lower_grade {m n : ℕ} (h : m ≤ n) :
      ∀ i y, y ∈ gradingQ n i → lower h y ∈ gradingQ m i := by
    rintro i _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  let Approx (n : ℕ) := {g : B →ₐ[k] (S ⧸ I ^ n) //
    g.comp α = (mk n).comp f ∧ ∀ i b, b ∈ gradingB i → g b ∈ gradingQ n i}
  have step (n : ℕ) (hn : 1 ≤ n) (g : Approx n) :
      ∃ next : Approx (n + 1), (lower n.le_succ).comp next.val = g.val := by
    have hsur : Function.Surjective (lower n.le_succ) := fun y ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨mk _ s, rfl⟩
    obtain ⟨z, hz, hzα, hzg⟩ := exists_graded_relative_lift gradingA gradingB
      (gradingQ (n + 1)) (gradingQ n) α hα hαg (lower n.le_succ) hsur
      (square_zero_quotient_factor I hn) (lower_grade n.le_succ) g.val g.property.2
      ((mk (n + 1)).comp f) (fun i a ha ↦ ⟨f a, hfg i a ha, rfl⟩) (by
        rw [g.property.1, ← AlgHom.comp_assoc]
        rfl)
    exact ⟨⟨z, hzα, hzg⟩, hz⟩
  let tower : (n : ℕ) → Approx (n + 1) :=
    fun n ↦ Nat.rec (motive := fun n ↦ Approx (n + 1)) ⟨e, he, heg⟩
      (fun j g ↦ (step (j + 1) (Nat.succ_pos j) g).choose) n
  let approx : (n : ℕ) → B →ₐ[k] (S ⧸ I ^ n)
    | 0 => (lower (Nat.zero_le 1)).comp e
    | n + 1 => (tower n).val
  have hsucc (n : ℕ) : (lower n.le_succ).comp (approx (n + 1)) = approx n := by
    cases n with
    | zero => rfl
    | succ n => exact (step (n + 1) (Nat.succ_pos n) (tower n)).choose_spec
  have hle {m n : ℕ} (hmn : m ≤ n) : (lower hmn).comp (approx n) = approx m := by
    induction n, hmn using Nat.le_induction with
    | base => simp [lower]
    | succ n hmn ih =>
      have hh := Ideal.Quotient.factorₐ_comp k (Ideal.pow_le_pow_right (I := I) n.le_succ)
        (Ideal.pow_le_pow_right (I := I) hmn)
      change (lower hmn).comp (lower n.le_succ) = lower (le_trans hmn n.le_succ) at hh
      rw [← hh, AlgHom.comp_assoc, hsucc, ih]
  have happrox (n : ℕ) : (approx n).comp α = (mk n).comp f := by
    cases n with
    | zero =>
      rw [show approx 0 = (lower (Nat.zero_le 1)).comp e from rfl, AlgHom.comp_assoc, he,
        ← AlgHom.comp_assoc]
      rfl
    | succ n => exact (tower n).property.1
  let G := AdicCompletion.liftAlgHom I approx hle
  let embedding : S →ₐ[k] AdicCompletion I S := IsScalarTower.toAlgHom k S (AdicCompletion I S)
  have hembedding (n : ℕ) (s : S) : AdicCompletion.evalₐ I n (embedding s) = mk n s :=
    AdicCompletion.evalₐ_of I n s
  have diagonal_injective : Function.Injective embedding := by
    intro a b h
    have hmem (n : ℕ) : a - b ∈ I ^ n := by
      apply Ideal.Quotient.eq.mp
      change mk n a = mk n b
      simpa only [hembedding] using congrArg (AdicCompletion.evalₐ I n) h
    apply sub_eq_zero.mp
    apply (DirectSum.decompose gradingS).injective
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    obtain ⟨n, hn⟩ := bounded i
    exact (hn _ (DirectSum.decompose gradingS (a - b) i).property (stable n i _ (hmem n))).trans
      (by simp)
  have in_degree {i : ℤ} {b : B} (hb : b ∈ gradingB i) :
      ∃ s ∈ gradingS i, embedding s = G b := by
    obtain ⟨n, hn⟩ := bounded i
    obtain ⟨s, hs, heq⟩ := (tower n).property.2 i b hb
    have hlarge (m : ℕ) (hm : n + 1 ≤ m) : mk m s = approx m b := by
      obtain ⟨r, hr, hr'⟩ := (show approx m b ∈ gradingQ m i from by
        cases m with
        | zero => omega
        | succ m => exact (tower m).property.2 i b hb)
      have hsr : mk (n + 1) s = mk (n + 1) r := by
        rw [← mk_lower hm r, show mk m r = approx m b from hr']
        exact heq.trans (DFunLike.congr_fun (hle hm) b).symm
      have hsub : s - r ∈ gradingS i := (gradingS i).sub_mem hs hr
      have hmem : s - r ∈ I ^ (n + 1) := Ideal.Quotient.eq.mp hsr
      have H := hn _ hsub (Ideal.pow_le_pow_right n.le_succ hmem)
      rwa [sub_eq_zero.mp H]
    refine ⟨s, hs, AdicCompletion.ext_evalₐ fun m ↦ ?_⟩
    rw [hembedding, AdicCompletion.evalₐ_liftAlgHom]
    by_cases hm : n + 1 ≤ m
    · exact hlarge m hm
    · have hl : m ≤ n + 1 := by omega
      rw [← mk_lower hl s, hlarge (n + 1) le_rfl]
      exact DFunLike.congr_fun (hle hl) b
  have hG (b : B) : G b ∈ embedding.range := by
    refine graded_induction gradingB (fun b ↦ G b ∈ embedding.range) b ?_ (by simp) ?_
    · intro i b hb
      obtain ⟨s, _, hs⟩ := in_degree hb
      exact ⟨s, hs⟩
    · intro b d hb hd
      rw [map_add]
      exact embedding.range.add_mem hb hd
  let g := (AlgEquiv.ofInjective embedding diagonal_injective).symm.toAlgHom.comp (G.codRestrict embedding.range hG)
  have hg (b : B) : embedding (g b) = G b :=
    congrArg Subtype.val ((AlgEquiv.ofInjective embedding diagonal_injective).apply_symm_apply ⟨G b, hG b⟩)
  refine ⟨g, ?_, ?_, ?_⟩
  · ext a
    apply diagonal_injective
    rw [AlgHom.comp_apply, hg]
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [AdicCompletion.evalₐ_liftAlgHom, hembedding]
    exact DFunLike.congr_fun (happrox n) a
  · ext b
    change mk 1 (g b) = e b
    rw [← hembedding, hg, AdicCompletion.evalₐ_liftAlgHom]
  · intro i b hb
    obtain ⟨s, hs, heq⟩ := in_degree hb
    exact diagonal_injective ((hg b).trans heq.symm) ▸ hs

private abbrev polynomialGrades (k : Type u) [Field k] :=
  AddMonoidAlgebra.gradeBy k (Int.ofNatHom : ℕ →+ ℤ)

private instance : GradedAlgebra (polynomialGrades k) :=
  AddMonoidAlgebra.gradeBy.gradedAlgebra (R := k) (Int.ofNatHom : ℕ →+ ℤ)

private abbrev polynomialVariable (k : Type u) [Field k] : AddMonoidAlgebra k ℕ :=
  Polynomial.toFinsuppIsoAlg k Polynomial.X

private abbrev parameterIdeal (k : Type u) [Field k] : Ideal (AddMonoidAlgebra k ℕ) :=
  Ideal.span {polynomialVariable k}

private theorem mem_parameterIdeal_pow {s : AddMonoidAlgebra k ℕ} {n : ℕ} :
    s ∈ parameterIdeal k ^ n ↔ ∀ d < n, s.coeff d = 0 := by
  let e := (Polynomial.toFinsuppIsoAlg k).symm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_dvd_iff e, map_pow]
  rw [show e (polynomialVariable k) = Polynomial.X from (Polynomial.toFinsuppIsoAlg k).symm_apply_apply _]
  exact Polynomial.X_pow_dvd_iff

private theorem coeff_eq_zero_of_wrong_degree {s : AddMonoidAlgebra k ℕ}
    {i : ℤ} {n : ℕ} (hs : s ∈ polynomialGrades k i) (hn : (n : ℤ) ≠ i) :
    s.coeff n = 0 := by
  by_contra hc
  exact hn (hs n (Finsupp.mem_support_iff.mpr hc))

private theorem parameterIdeal_stable (n : ℕ) (i : ℤ) (s : AddMonoidAlgebra k ℕ)
    (hs : s ∈ parameterIdeal k ^ n) :
    GradedAlgebra.proj (polynomialGrades k) i s ∈ parameterIdeal k ^ n := by
  rw [mem_parameterIdeal_pow] at hs ⊢
  have hp (d : ℕ) (s : AddMonoidAlgebra k ℕ) :
      (GradedAlgebra.proj (polynomialGrades k) i s).coeff d =
        if (d : ℤ) = i then s.coeff d else 0 := by
    refine graded_induction (polynomialGrades k)
      (fun s ↦ (GradedAlgebra.proj (polynomialGrades k) i s).coeff d =
        if (d : ℤ) = i then s.coeff d else 0) s ?_ (by simp) ?_
    · intro j x hx
      by_cases h : j = i
      · subst j
        rw [proj_of_mem _ hx]
        by_cases hd : (d : ℤ) = i
        · rw [ite_eq_left hd]
        · rw [ite_eq_right hd, coeff_eq_zero_of_wrong_degree hx hd]
      · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ hx h]
        by_cases hd : (d : ℤ) = i
        · rw [ite_eq_left hd, coeff_eq_zero_of_wrong_degree hx (hd.trans_ne (Ne.symm h))]
          rfl
        · rw [ite_eq_right hd]
          rfl
    · intro x y hx hy
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
      by_cases ht : (d : ℤ) = i <;> simp [ht, AddMonoidAlgebra.coeff_add]
  intro d hd
  rw [hp, hs d hd, ite_self]

private theorem parameterIdeal_bounded (i : ℤ) :
    ∃ n, ∀ s ∈ polynomialGrades k i, s ∈ parameterIdeal k ^ n → s = 0 := by
  refine ⟨i.toNat + 1, fun s hs hn ↦ ?_⟩
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro d
  change s.coeff d = 0
  by_cases hd : (d : ℤ) = i
  · exact mem_parameterIdeal_pow.mp hn d (by omega)
  · exact coeff_eq_zero_of_wrong_degree hs hd

private theorem exists_graded_polynomial_lift
    (gradingA : ℤ → Submodule k A) [GradedAlgebra gradingA]
    (gradingB : ℤ → Submodule k B) [GradedAlgebra gradingB]
    (α : A →ₐ[k] B) (hα : α.toRingHom.FormallySmooth)
    (hαg : ∀ i a, a ∈ gradingA i → α a ∈ gradingB i)
    (f : A →ₐ[k] AddMonoidAlgebra k ℕ)
    (hfg : ∀ i a, a ∈ gradingA i → f a ∈ polynomialGrades k i)
    (e : B →ₐ[k] k) (he : ∀ a, e (α a) = (f a).coeff 0)
    (heg : ∀ i b, b ∈ gradingB i → i ≠ 0 → e b = 0) :
    ∃ g : B →ₐ[k] AddMonoidAlgebra k ℕ, g.comp α = f ∧
      (∀ b, (g b).coeff 0 = e b) ∧
      (∀ i b, b ∈ gradingB i → g b ∈ polynomialGrades k i) := by
  classical
  let q := Ideal.Quotient.mkₐ k (parameterIdeal k ^ 1)
  let c := Algebra.ofId k (AddMonoidAlgebra k ℕ)
  let e' := q.comp (c.comp e)
  have hc (r : k) : (c r).coeff 0 = r := by
    change (AddMonoidAlgebra.single 0 r).coeff 0 = r
    simp
  have he' : e'.comp α = q.comp f := by
    ext a
    change q (c (e (α a))) = q (f a)
    apply Ideal.Quotient.eq.mpr
    apply mem_parameterIdeal_pow.mpr
    intro d hd
    have h : d = 0 := by omega
    rw [h, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hc, he, sub_self]
  have hgrade i b (hb : b ∈ gradingB i) : e' b ∈
      quotientGrading (polynomialGrades k) (parameterIdeal k ^ 1) i := by
    refine ⟨c (e b), ?_, rfl⟩
    by_cases hi : i = 0
    · subst i
      exact SetLike.algebraMap_mem_graded _ _
    · rw [heg i b hb hi, map_zero]
      exact (polynomialGrades k i).zero_mem
  obtain ⟨g, hg, hge, hgg⟩ := exists_graded_lift_of_powers gradingA gradingB
    (polynomialGrades k) (parameterIdeal k) parameterIdeal_stable parameterIdeal_bounded
    α hα hαg f hfg e' he' hgrade
  refine ⟨g, hg, ?_, hgg⟩
  intro b
  have eq' : q (g b) = q (c (e b)) := DFunLike.congr_fun hge b
  have hv := mem_parameterIdeal_pow.mp (Ideal.Quotient.eq.mp eq') 0 Nat.zero_lt_one
  rwa [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hc, sub_eq_zero] at hv

end GradedLifting


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial TensorProduct

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.RationalContraction
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra diagonalGroup)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics DiagonalizableFixedLocus WeightDecomposition

open private affineSpectrum affinePointEquiv affinePointEquiv_natural parameter_zpow specFF
  from LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private conjugationAction reflectAction coordinateCoaction diagonalSource
  hom_of_weight weight_mul weight_algebraMap affine_fixed_criterion
  isFixedBy_comp_equivariant isFixedBy_of_comp_equivariant
  from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private restrictGroupAction restrictGroupAction_smul orbitMap_comp orbitMap_equivariant
  rightTranslateProduct isPullback_tensor_structure
  from LinearAlgebraicGroups.Flag.SmoothOrbit

open private weight_isInternal from LinearAlgebraicGroups.Multiplicative.WeightDecomposition

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme k} {X Y : SchemeOver k}

private abbrev Gm (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

local instance (k : Type u) [Field k] : (testSpec k).Braided :=
  braidedAlgSpec (R := CommRingCat.of k)

private abbrev specMap {A B : TestAlgebra k} (f : A →ₐ[k] B) :
    affineSpectrum B ⟶ affineSpectrum A :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private def pullbackCoordinates {A B : TestAlgebra k} (eA : affineSpectrum A ≅ X)
    (eB : affineSpectrum B ≅ Y) (q : Y ⟶ X) : A →ₐ[k] B :=
  ((specFF k).preimage (eB.hom ≫ q ≫ eA.inv)).unop.hom

private theorem specMap_pullbackCoordinates {A B : TestAlgebra k}
    (eA : affineSpectrum A ≅ X) (eB : affineSpectrum B ≅ Y) (q : Y ⟶ X) :
    specMap (pullbackCoordinates eA eB q) = eB.hom ≫ q ≫ eA.inv :=
  (specFF k).map_preimage _

private theorem affinePointEquiv_comp {A B R : TestAlgebra k} (eA : affineSpectrum A ≅ X)
    (eB : affineSpectrum B ≅ Y) (q : Y ⟶ X) (v : B →ₐ[k] R) :
    affinePointEquiv eA R (v.comp (pullbackCoordinates eA eB q)) =
      affinePointEquiv eB R v ≫ q := by
  change specMap (v.comp (pullbackCoordinates eA eB q)) ≫ eA.hom =
    (specMap v ≫ eB.hom) ≫ q
  rw [show specMap (v.comp (pullbackCoordinates eA eB q)) =
      specMap v ≫ specMap (pullbackCoordinates eA eB q) from
    (testSpec k).map_comp (CommAlgCat.ofHom v).op (CommAlgCat.ofHom (pullbackCoordinates eA eB q)).op,
    specMap_pullbackCoordinates]
  simp

private theorem pullbackCoordinates_formallySmooth {A B : TestAlgebra k}
    (eA : affineSpectrum A ≅ X) (eB : affineSpectrum B ≅ Y) (q : Y ⟶ X)
    (hq : Smooth q.left) : (pullbackCoordinates eA eB q).toRingHom.FormallySmooth := by
  let F : SchemeOver k ⥤ Scheme := Over.forget _
  have : IsIso eA.inv.left := F.map_isIso eA.inv
  have : IsIso eB.hom.left := F.map_isIso eB.hom
  let := hq
  have h : Smooth (specMap (pullbackCoordinates eA eB q)).left := by
    rw [specMap_pullbackCoordinates]
    change Smooth (eB.hom.left ≫ q.left ≫ eA.inv.left)
    infer_instance
  change Smooth (Spec.map (CommRingCat.ofHom (pullbackCoordinates eA eB q).toRingHom)) at h
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact h.formallySmooth

/-- The grading of an algebra of functions for a split cocharacter action. -/
private abbrev weightGrading {A : Type u} [CommRing A] [Algebra k A]
    (ρ : CoordinateCoaction (k := k) (M := IntegerCharacters.{u}) (A := A))
    (n : ℤ) : Submodule k A :=
  weightSpace ρ.toRightComodule (⟨Multiplicative.ofAdd n⟩ : IntegerCharacters)

@[instance_reducible] private def weightGradedAlgebra {A : Type u} [CommRing A] [Algebra k A]
    (ρ : CoordinateCoaction (k := k) (M := IntegerCharacters.{u}) (A := A)) :
    GradedAlgebra (weightGrading ρ) := by
  let f : ℤ ≃ IntegerCharacters.{u} := (Equiv.ulift (α := Multiplicative ℤ)).symm
  have h := weight_isInternal ρ.toRightComodule
  let D : DirectSum.Decomposition (weightGrading ρ) :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (show iSupIndep (weightGrading ρ) from h.submodule_iSupIndep.comp f.injective)
      (show (⨆ i, weightGrading ρ i) = ⊤ from
        (f.surjective.iSup_comp (weightSpace ρ.toRightComodule)).trans h.submodule_iSup_eq_top)
    ).chooseDecomposition
  exact { toDecomposition := D
          one_mem := by
            change 1 ∈ weightSpace ρ.toRightComodule 1
            simpa using weight_algebraMap ρ (1 : k)
          mul_mem := by
            intro i j x y hi hj
            exact weight_mul ρ hi hj }

private abbrev onAffineSpectrum {A : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) : ModObj (Gm k).X (affineSpectrum A) :=
  letI := a
  letI : IsMonHom (Iso.refl (Gm k).X).hom := by change IsMonHom (𝟙 _); infer_instance
  ModObj.ofIso (Iso.refl (Gm k).X) e.symm

private theorem onAffineSpectrum_smul {A : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) :
    (onAffineSpectrum e a).smul ≫ e.hom = (𝟙 (Gm k).X ⊗ₘ e.hom) ≫ a.smul := by
  change ((𝟙 (Gm k).X ⊗ₘ e.hom) ≫ a.smul ≫ e.inv) ≫ e.hom = _
  simp

private abbrev affineAction {A : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) :=
  reflectAction (testSpec k) (specFF k) (diagonalSource (k := k) (M := IntegerCharacters.{u}))
    (op A) (onAffineSpectrum e a)

private abbrev affineCoaction {A : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) :=
  coordinateCoaction (affineAction e a)

private theorem affineAction_map {A : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) :
    (testSpec k).map (affineAction e a).smul =
      CartesianMonoidalCategory.prodComparison (testSpec k) (diagonalSource (k := k) (M := IntegerCharacters.{u}))
        (op A) ≫ (onAffineSpectrum e a).smul := by
  change (testSpec k).map ((specFF k).preimage
    (Functor.OplaxMonoidal.δ (testSpec k) _ _ ≫ (onAffineSpectrum e a).smul)) = _
  rw [(specFF k).map_preimage, Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
  rfl

private theorem affineAction_onWeight {A R : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) (t : Rˣ) (v : A →ₐ[k] R)
    {n : ℤ} {z : A} (hz : z ∈ weightGrading (affineCoaction e a) n) :
    (affinePointEquiv e R).symm
      (lift (unitPoint R t) (affinePointEquiv e R v) ≫ a.smul) z =
      unitCoordinates R t (MonoidAlgebra.of k IntegerCharacters.{u} ⟨Multiplicative.ofAdd n⟩) *
        v z := by
  let F := testSpec k
  let T := diagonalSource (k := k) (M := IntegerCharacters.{u})
  let s : op R ⟶ T := (CommAlgCat.ofHom (unitCoordinates R t)).op
  let c : op R ⟶ op A := (CommAlgCat.ofHom v).op
  let l := (affineAction e a).smul
  have hpair : F.map (lift s c) ≫ CartesianMonoidalCategory.prodComparison F T (op A) = lift (F.map s) (F.map c) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst, ← F.map_comp, lift_fst]
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, ← F.map_comp, lift_snd]
  have heq : affinePointEquiv e R ((lift s c ≫ l).unop.hom) =
      lift (unitPoint R t) (affinePointEquiv e R v) ≫ a.smul := by
    change F.map (lift s c ≫ l) ≫ e.hom = _
    rw [F.map_comp, affineAction_map, ← Category.assoc, hpair, Category.assoc,
      onAffineSpectrum_smul, lift_map_assoc]
    change lift ((unitPoint R t : Points (Gm k).X R) ≫ 𝟙 _) (F.map c ≫ e.hom) ≫ a.smul = _
    rw [Category.comp_id]
    rfl
  rw [← heq, Equiv.symm_apply_apply]
  let B := MonoidAlgebra k IntegerCharacters.{u}
  let w := MonoidAlgebra.of k IntegerCharacters.{u} ⟨Multiplicative.ofAdd n⟩
  have hweight := hom_of_weight (affineCoaction e a) hz
  change (Algebra.TensorProduct.comm k B A) (l.unop.hom z) = z ⊗ₜ[k] w at hweight
  have he : l.unop.hom z = w ⊗ₜ[k] z := by
    apply (Algebra.TensorProduct.comm k B A).injective
    rw [hweight, Algebra.TensorProduct.comm_tmul]
  change (lift s c).unop.hom (l.unop.hom z) = _
  rw [he, CommAlgCat.lift_unop_hom]
  change Algebra.TensorProduct.lift (unitCoordinates R t) v (fun _ _ ↦ .all _ _)
    (w ⊗ₜ[k] z) = _
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem pullbackCoordinates_graded {A B : TestAlgebra k}
    (eA : affineSpectrum A ≅ X) (eB : affineSpectrum B ≅ Y)
    (a : ModObj (Gm k).X X) (b : ModObj (Gm k).X Y) (q : Y ⟶ X)
    (hq : b.smul ≫ q = (𝟙 (Gm k).X ⊗ₘ q) ≫ a.smul)
    (n : ℤ) (z : A) (hz : z ∈ weightGrading (affineCoaction eA a) n) :
    pullbackCoordinates eA eB q z ∈ weightGrading (affineCoaction eB b) n := by
  let F := testSpec k
  let T := diagonalSource (k := k) (M := IntegerCharacters.{u})
  let q' : op B ⟶ op A := (CommAlgCat.ofHom (pullbackCoordinates eA eB q)).op
  let lA := (affineAction eA a).smul
  let lB := (affineAction eB b).smul
  have hq' : F.map q' = eB.hom ≫ q ≫ eA.inv :=
    specMap_pullbackCoordinates eA eB q
  have he : (onAffineSpectrum eB b).smul ≫ F.map q' =
      (𝟙 (Gm k).X ⊗ₘ F.map q') ≫ (onAffineSpectrum eA a).smul := by
    have hcomp : F.map q' ≫ eA.hom = eB.hom ≫ q := by simp [hq']
    apply (cancel_mono eA.hom).mp
    calc
      _ = ((onAffineSpectrum eB b).smul ≫ eB.hom) ≫ q := by
        simp only [Category.assoc, hcomp]
      _ = (𝟙 (Gm k).X ⊗ₘ eB.hom) ≫ b.smul ≫ q := by
        rw [onAffineSpectrum_smul, Category.assoc]
      _ = (𝟙 (Gm k).X ⊗ₘ (eB.hom ≫ q)) ≫ a.smul := by
        rw [hq, tensorHom_comp_tensorHom_assoc, Category.id_comp]
      _ = _ := by
        rw [Category.assoc, onAffineSpectrum_smul, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, hcomp]
  have hreflect : lB ≫ q' = (𝟙 T ⊗ₘ q') ≫ lA := by
    apply (specFF k).map_injective
    change F.map (lB ≫ q') = F.map ((𝟙 T ⊗ₘ q') ≫ lA)
    have hlA := affineAction_map eA a
    have hlB := affineAction_map eB b
    change F.map lA = CartesianMonoidalCategory.prodComparison F T (op A) ≫ _ at hlA
    change F.map lB = CartesianMonoidalCategory.prodComparison F T (op B) ≫ _ at hlB
    change _ = (𝟙 (F.obj T) ⊗ₘ F.map q') ≫ (onAffineSpectrum eA a).smul at he
    rw [F.map_comp, F.map_comp, hlA, hlB, Category.assoc, he,
      CartesianMonoidalCategory.prodComparison_natural_assoc, F.map_id]
  let C := MonoidAlgebra k IntegerCharacters.{u}
  let w := MonoidAlgebra.of k IntegerCharacters.{u} ⟨Multiplicative.ofAdd n⟩
  have hweight := hom_of_weight (affineCoaction eA a) hz
  change (Algebra.TensorProduct.comm k C A) (lA.unop.hom z) = z ⊗ₜ[k] w at hweight
  have ha : lA.unop.hom z = w ⊗ₜ[k] z := by
    apply (Algebra.TensorProduct.comm k C A).injective
    rw [hweight, Algebra.TensorProduct.comm_tmul]
  have hb := congrArg (fun f ↦ f.unop.hom z) hreflect
  change lB.unop.hom (pullbackCoordinates eA eB q z) =
    Algebra.TensorProduct.map (AlgHom.id k C) (pullbackCoordinates eA eB q) (lA.unop.hom z) at hb
  apply mem_weightSpace.mpr
  change Algebra.TensorProduct.comm k C B (lB.unop.hom (pullbackCoordinates eA eB q z)) = _
  rw [hb, ha, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
  rfl

/-- Pulling back a point along a constant map picks out weight zero precisely
when that point is fixed by the acting torus. -/
private theorem affinePoint_fixed_iff {A : TestAlgebra k}
    (e : affineSpectrum A ≅ X) (a : ModObj (Gm k).X X) (v : A →ₐ[k] k) :
    IsFixedBy a.smul (affinePointEquiv e (groundField k) v) ↔
      ∀ n ≠ 0, ∀ z ∈ weightGrading (affineCoaction e a) n, v z = 0 := by
  let w := specMap (B := groundField k) v
  have he : (onAffineSpectrum e a).smul ≫ e.hom = ((Gm k).X ◁ e.hom) ≫ a.smul := by
    rw [onAffineSpectrum_smul, tensorHom_def, id_whiskerRight, Category.id_comp]
  have htransport : IsFixedBy a.smul (affinePointEquiv e (groundField k) v) ↔
      IsFixedBy (onAffineSpectrum e a).smul w :=
    ⟨isFixedBy_of_comp_equivariant he, isFixedBy_comp_equivariant he⟩
  have hcriterion : IsFixedBy (onAffineSpectrum e a).smul w ↔
      fixedIdeal (affineCoaction e a) ≤ RingHom.ker v :=
    affine_fixed_criterion (M := IntegerCharacters) (onAffineSpectrum e a) v
  rw [htransport, hcriterion]
  rw [fixedIdeal, Ideal.span_le]
  constructor
  · intro h n hn z hz
    refine RingHom.mem_ker.mp (h ⟨⟨Multiplicative.ofAdd n⟩, ?_, hz⟩)
    exact fun hc ↦ hn (congrArg (fun m : IntegerCharacters.{u} ↦ m.down.toAdd) hc)
  · rintro h z ⟨⟨m⟩, hm, hz⟩
    exact RingHom.mem_ker.mpr (h m.toAdd (fun hc ↦ hm (ULift.ext hc)) z hz)

private theorem productRight_isPullback (q : Y ⟶ X) (D : SchemeOver k) :
    IsPullback (q ⊗ₘ 𝟙 D) (fst Y D) (fst X D) q := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T r s h₁ h₂
    apply CartesianMonoidalCategory.hom_ext r s h₂
    simpa only [Category.assoc, tensorHom_snd, Category.comp_id] using
      congrArg (fun f ↦ f ≫ snd X D) h₁
  · intro T r s h
    refine ⟨lift s (r ≫ snd X D), ?_, by simp⟩
    apply CartesianMonoidalCategory.hom_ext <;> simp [h]

/-- Smoothness of one surjective orbit map transfers to every rational point
by translation over the fibre of the first orbit map. -/
private theorem smooth_orbitMap_of_surjective (a : ModObj G.X X)
    (hG : IsAffine G.X.left) (hX : IsAffine X.left)
    (y z : 𝟙_ (SchemeOver k) ⟶ X)
    (hs : Smooth (Specs.SmoothOrbit.orbitMap a y).left)
    (he : Surjective (Specs.SmoothOrbit.orbitMap a y).left) :
    Smooth (Specs.SmoothOrbit.orbitMap a z).left := by
  let := a
  let q := Specs.SmoothOrbit.orbitMap a y
  let r := Specs.SmoothOrbit.orbitMap a z
  let D := pullback q z
  let d : D ⟶ G.X := pullback.fst q z
  let v : D ⟶ 𝟙_ (SchemeOver k) := pullback.snd q z
  let F : SchemeOver k ⥤ Scheme := Over.forget _
  have pb : IsPullback d.left v.left q.left z.left :=
    (IsPullback.of_hasPullback q z).map F
  have : Surjective v.left := MorphismProperty.of_isPullback pb he
  have : Smooth v.left := MorphismProperty.of_isPullback pb hs
  let := hG
  let := hX
  have hv : v.left = D.hom := by
    have h := Over.w v
    change v.left ≫ 𝟙 _ = D.hom at h
    simpa only [Category.comp_id] using h
  have hsur : Surjective D.hom := hv ▸ inferInstanceAs (Surjective v.left)
  have hflat : Flat D.hom := hv ▸ inferInstanceAs (Flat v.left)
  have hqc : QuasiCompact D.hom := hv ▸
    MorphismProperty.of_isPullback (P := @QuasiCompact) pb
      (inferInstanceAs (QuasiCompact q.left))
  have hp : d ≫ q = toUnit D ≫ z :=
    pullback.condition.trans (congrArg (· ≫ z) (toUnit_unique v (toUnit D)))
  let φ := rightTranslateProduct d
  have htranslate : φ.hom ≫ (q ⊗ₘ 𝟙 D) = r ⊗ₘ 𝟙 D := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.assoc, tensorHom_fst,
      tensorHom_snd, Category.comp_id, φ, rightTranslateProduct, lift_fst_assoc, lift_snd]
    rw [orbitMap_comp, mul_smul, ← orbitMap_comp, Category.assoc, hp, comp_toUnit_assoc,
      orbitMap_comp]
  have hqs : Smooth (q ⊗ₘ 𝟙 D).left :=
    MorphismProperty.of_isPullback ((productRight_isPullback q D).map F).flip hs
  have hrs : Smooth (r ⊗ₘ 𝟙 D).left := by
    rw [← htranslate, Over.comp_left]
    have : IsIso φ.hom.left := F.map_isIso φ.hom
    infer_instance
  have hbase := isPullback_tensor_structure X D
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ((productRight_isPullback r D).map F)
      ⟨⟨MorphismProperty.of_isPullback hbase.flip hsur,
        MorphismProperty.of_isPullback hbase.flip hflat⟩,
        MorphismProperty.of_isPullback hbase.flip hqc⟩ hrs

private theorem stabilizes_comp {T U : SchemeOver k} (a : ModObj G.X X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) {g : T ⟶ G.X}
    (h : Stabilizes a.smul x g) (s : U ⟶ T) :
    Stabilizes a.smul x (s ≫ g) := by
  simpa only [Stabilizes, Category.assoc, comp_lift_assoc, comp_toUnit_assoc] using
    congrArg (s ≫ ·) h

private theorem fixed_cocharacter (a : ModObj G.X X) (c : Cocharacter G)
    (x : Points X (groundField k)) (h : IsFixedBy (restrictGroupAction c a).smul x) :
    Stabilizes a.smul ((groundPointIso k).hom ≫ x) c.hom.hom := by
  have hh := congrArg (lift (𝟙 (Gm k).X) (toUnit _ ≫ (groundPointIso k).hom) ≫ ·) h
  simpa only [IsFixedBy, Stabilizes, restrictGroupAction_smul, Category.assoc,
    lift_whiskerLeft_assoc, lift_map_assoc, Category.id_comp, lift_snd_assoc, Category.comp_id]
      using hh

private theorem orbitMap_cocharacter_equivariant (a : ModObj G.X X) (c : Cocharacter G)
    (x : 𝟙_ (SchemeOver k) ⟶ X) (hx : Stabilizes a.smul x c.hom.hom) :
    (conjugationAction c).smul ≫ Specs.SmoothOrbit.orbitMap a x =
      (𝟙 (Gm k).X ⊗ₘ Specs.SmoothOrbit.orbitMap a x) ≫ (restrictGroupAction c a).smul := by
  let := a
  let T := (Gm k).X ⊗ G.X
  let l : T ⟶ G.X := fst (Gm k).X G.X ≫ c.hom.hom
  let g : T ⟶ G.X := snd (Gm k).X G.X
  have hfix : l • (toUnit T ≫ x) = toUnit T ≫ x :=
    stabilizes_comp a x hx (fst (Gm k).X G.X)
  have hinv : l⁻¹ • (toUnit T ≫ x) = toUnit T ≫ x :=
    (congrArg (l⁻¹ • ·) hfix.symm).trans (inv_smul_smul l (toUnit T ≫ x))
  have hconj : (conjugationAction c).smul = l * g * l⁻¹ := by
    change (c.hom.hom ▷ G.X) ≫ GrpObj.conj G.X = _
    have hpair : c.hom.hom ▷ G.X = lift l g := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [l]
      · simp [g]
    rw [hpair, GrpObj.lift_conj_eq_mul_mul_inv]
  rw [hconj, orbitMap_comp, mul_smul, mul_smul]
  change l • (g • (l⁻¹ • (toUnit T ≫ x))) = _
  rw [hinv, ← orbitMap_comp]
  rw [restrictGroupAction_smul, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  change lift l (g ≫ Specs.SmoothOrbit.orbitMap a x) ≫ a.smul = _
  rw [← lift_fst_comp_snd_comp]
  simp only [l, g, Category.comp_id]

private theorem pointCoordinates_map {A R S : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (f : R ⟶ S) (x : Points X R) :
    (affinePointEquiv e S).symm (mapPoints f x) =
      f.hom.comp ((affinePointEquiv e R).symm x) := by
  apply (affinePointEquiv e S).injective
  rw [Equiv.apply_symm_apply, affinePointEquiv_natural, Equiv.apply_symm_apply]

private theorem laurentAction_onWeight {A R : TestAlgebra k} (e : affineSpectrum A ≅ X)
    (a : ModObj (Gm k).X X) (x : Points X R)
    {n : ℤ} {z : A} (hz : z ∈ weightGrading (affineCoaction e a) n) :
    (affinePointEquiv e (laurentAlgebra R)).symm
      (lift (unitPoint (laurentAlgebra R) (laurentParameter R))
        (mapPoints (laurentConstants R) x) ≫ a.smul) z =
      AddMonoidAlgebra.single n ((affinePointEquiv e R).symm x z) := by
  let v := (affinePointEquiv e R).symm x
  have hv := (affinePointEquiv_natural e (laurentConstants R) v).trans
    (congrArg (mapPoints (laurentConstants R)) (Equiv.apply_symm_apply (affinePointEquiv e R) x))
  rw [← hv, affineAction_onWeight e a _ _ hz, LaurentPolynomial.single_eq_C_mul_T, mul_comm]
  change LaurentPolynomial.C (v z) * unitCoordinates (laurentAlgebra R) (laurentParameter R)
      (MonoidAlgebra.of k IntegerCharacters.{u} ⟨Multiplicative.ofAdd n⟩) = _
  congr 1
  rw [unitCoordinates, MonoidAlgebra.lift_of]
  exact parameter_zpow R n

private theorem lift_restricted_smul (c : Cocharacter G) (a : ModObj G.X X)
    {T : SchemeOver k} (s : T ⟶ (Gm k).X) (x : T ⟶ X) :
    lift s x ≫ (restrictGroupAction c a).smul = lift (s ≫ c.hom.hom) x ≫ a.smul := by
  rw [restrictGroupAction_smul, lift_map_assoc, Category.comp_id]

private theorem lift_conjugation_smul (c : Cocharacter G)
    {T : SchemeOver k} (s : T ⟶ (Gm k).X) (g : T ⟶ G.X) :
    lift s g ≫ (conjugationAction c).smul =
      (s ≫ c.hom.hom) * g * (s ≫ c.hom.hom)⁻¹ := by
  change lift s g ≫ (c.hom.hom ▷ G.X) ≫ GrpObj.conj G.X = _
  simp only [lift_whiskerRight_assoc, GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst, lift_snd]

private theorem polynomialGrade_iff {n : ℤ} {p : Polynomial k} :
    Polynomial.toFinsuppIsoAlg k p ∈ polynomialGrades k n ↔
      ∀ d : ℕ, (d : ℤ) ≠ n → p.coeff d = 0 := by
  constructor
  · exact fun h d hd ↦ coeff_eq_zero_of_wrong_degree h hd
  · intro h d hd
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hd) (h d hn)

private theorem polynomialGrade_of_toLaurent_eq_single {p : Polynomial k} {n : ℤ} {r : k}
    (h : p.toLaurent = AddMonoidAlgebra.single n r) :
    Polynomial.toFinsuppIsoAlg k p ∈ polynomialGrades k n := by
  rw [polynomialGrade_iff]
  intro d hd
  rw [← coeff_toLaurent_nat, h, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    ite_eq_right (Ne.symm hd)]

private theorem toLaurent_of_polynomialGrade {p : Polynomial k} {n : ℤ}
    (hp : Polynomial.toFinsuppIsoAlg k p ∈ polynomialGrades k n) :
    p.toLaurent = AddMonoidAlgebra.single n (p.eval 1) := by
  rw [polynomialGrade_iff] at hp
  by_cases hn : 0 ≤ n
  · have he : p = Polynomial.monomial n.toNat (p.coeff n.toNat) := by
      apply Polynomial.ext
      intro d
      by_cases hd : d = n.toNat
      · simp [hd]
      · rw [hp d (by omega), Polynomial.coeff_monomial, ite_eq_right (Ne.symm hd)]
    rw [he, Polynomial.toLaurent_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      Int.toNat_of_nonneg hn, Polynomial.eval_monomial, one_pow, mul_one]
  · have he : p = 0 := Polynomial.ext fun d ↦ by simpa using hp d (by omega)
    simp [he]

private theorem eval_one_of_toLaurent_eq_single {p : Polynomial k} {n : ℤ} {r : k}
    (h : p.toLaurent = AddMonoidAlgebra.single n r) : p.eval 1 = r := by
  change p.eval₂ (RingHom.id k) ((1 : kˣ) : k) = r
  rw [← LaurentPolynomial.eval₂_toLaurent, h, LaurentPolynomial.single_eq_C_mul_T,
    map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
  simp

private theorem polynomialEvaluate_ground (d : k) (p : Polynomial k) :
    (polynomialEvaluate (groundField k) d).hom p = p.eval d := rfl

private theorem groundPoint_const {X : SchemeOver k} (x : Points X (groundField k)) :
    toUnit (affineSpectrum (groundField k)) ≫ (groundPointIso k).hom ≫ x = x := by
  have h := toUnit_unique (toUnit (affineSpectrum (groundField k))) (groundPointIso k).inv
  rw [h, Iso.inv_hom_id_assoc]

open private isFixedBy_conjugation_iff from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

/-- Lift the given polynomial family along the orbit map based at its limit.
The equivariant lift starts at the identity, so its value at one is contracted
to the identity by the same cocharacter. -/
private theorem rational_lift_of_smooth_orbitMap
    (hG : IsAffine G.X.left) (hX : IsAffine X.left) (a : ModObj G.X X)
    (hs : ∀ x : 𝟙_ (SchemeOver k) ⟶ X, Smooth (Specs.SmoothOrbit.orbitMap a x).left)
    (c : Cocharacter G) (x x₀ : Points X (groundField k))
    (hx : ActionHasLimit a c x x₀) :
    ∃ g : GroupPoints G (groundField k), HasLimit c g 1 ∧ lift g x₀ ≫ a.smul = x ∧
      Stabilizes a.smul ((groundPointIso k).hom ≫ x₀) c.hom.hom := by
  obtain ⟨A₀, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hX
  obtain ⟨B₀, ⟨d₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hG
  let A := A₀.unop
  let B := B₀.unop
  let e : affineSpectrum A ≅ X := e₀
  let d : affineSpectrum B ≅ G.X := d₀
  let R := groundField k
  let aT := restrictGroupAction c a
  let bT := conjugationAction c
  let U := weightGrading (affineCoaction e aT)
  let V := weightGrading (affineCoaction d bT)
  let : GradedAlgebra U := weightGradedAlgebra _
  let : GradedAlgebra V := weightGradedAlgebra _
  obtain ⟨curve, hcurve, hzero⟩ := hx
  let f := (affinePointEquiv e (polynomialAlgebra R)).symm curve
  let v := (affinePointEquiv e R).symm x
  let v₀ := (affinePointEquiv e R).symm x₀
  have hf₀ (z : A) : v₀ z = (f z).coeff 0 := by
    have h := pointCoordinates_map e (polynomialEvaluate (groundField k) 0) curve
    rw [hzero] at h
    rw [show v₀ = (polynomialEvaluate R 0).hom.comp f from h]
    change (polynomialEvaluate R 0).hom (f z) = _
    rw [polynomialEvaluate_ground, ← Polynomial.coeff_zero_eq_eval_zero]
  have hf {n : ℤ} {z : A} (hz : z ∈ U n) :
      (f z).toLaurent = AddMonoidAlgebra.single n (v z) := by
    have h := DFunLike.congr_fun (pointCoordinates_map e (polynomialToLaurent R) curve) z
    change _ = (f z).toLaurent at h
    rw [← h, hcurve]
    change (affinePointEquiv e (laurentAlgebra R)).symm
      (lift (unitPoint _ _ ≫ c.hom.hom) (mapPoints (laurentConstants R) x) ≫ a.smul) z = _
    rw [← lift_restricted_smul]
    exact laurentAction_onWeight e aT x hz
  have hfgrade : ∀ n z, z ∈ U n → Polynomial.toFinsuppIsoAlg k (f z) ∈ polynomialGrades k n :=
    fun _ _ hz ↦ polynomialGrade_of_toLaurent_eq_single (hf hz)
  have hx₀ : IsFixedBy aT.smul x₀ := by
    rw [← Equiv.apply_symm_apply (affinePointEquiv e R) x₀]
    apply (affinePoint_fixed_iff e aT v₀).mpr
    intro n hn z hz
    exact (hf₀ z).trans (coeff_eq_zero_of_wrong_degree (hfgrade n z hz) (by simpa using Ne.symm hn))
  have hxfix := fixed_cocharacter a c x₀ hx₀
  have hcurve1 : mapPoints (polynomialEvaluate R 1) curve = x := by
    apply (affinePointEquiv e R).symm.injective
    rw [pointCoordinates_map]
    apply AlgHom.ext
    intro z
    change (f z).eval 1 = v z
    refine graded_induction U (fun z ↦ (f z).eval 1 = v z) z ?_ (by simp [v]) ?_
    · intro n y hy
      exact eval_one_of_toLaurent_eq_single (hf hy)
    · intro y w hy hw
      simp only [map_add, Polynomial.eval_add, hy, hw]
  let x₀' := (groundPointIso k).hom ≫ x₀
  let q := Specs.SmoothOrbit.orbitMap a x₀'
  let α := pullbackCoordinates e d q
  have hα : α.toRingHom.FormallySmooth := pullbackCoordinates_formallySmooth e d q (hs x₀')
  have hαg : ∀ n z, z ∈ U n → α z ∈ V n :=
    pullbackCoordinates_graded e d aT bT q (orbitMap_cocharacter_equivariant a c x₀' hxfix)
  let ε := (affinePointEquiv d R).symm (1 : GroupPoints G R)
  have hq₀ : (1 : GroupPoints G R) ≫ q = x₀ := by
    let := a
    rw [orbitMap_comp, one_smul]
    exact groundPoint_const x₀
  have hε : ε.comp α = v₀ := by
    apply (affinePointEquiv e R).injective
    rw [affinePointEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hq₀]
  have hεg : ∀ n z, z ∈ V n → n ≠ 0 → ε z = 0 := by
    have h : IsFixedBy bT.smul (1 : GroupPoints G R) := by
      apply (isFixedBy_conjugation_iff c _).mpr
      simp [Centralizes, conjugateFamily]
    intro n z hz hn
    apply (affinePoint_fixed_iff d bT ε).mp _ n hn z hz
    rwa [Equiv.apply_symm_apply]
  let p := (Polynomial.toFinsuppIsoAlg k).toAlgHom.comp f
  obtain ⟨g₀, hgα, hg₀, hgg⟩ :=
    exists_graded_polynomial_lift U V α hα hαg p hfgrade ε
      (fun z ↦ (DFunLike.congr_fun hε z).trans (hf₀ z)) hεg
  let gP := (Polynomial.toFinsuppIsoAlg k).symm.toAlgHom.comp g₀
  let lifted := affinePointEquiv d (polynomialAlgebra R) gP
  let g : GroupPoints G R := mapPoints (polynomialEvaluate R 1) lifted
  have hgP : gP.comp α = f := by
    apply AlgHom.ext
    intro z
    change (Polynomial.toFinsuppIsoAlg k).symm (g₀ (α z)) = f z
    rw [show g₀ (α z) = Polynomial.toFinsuppIsoAlg k (f z) from DFunLike.congr_fun hgα z,
      AlgEquiv.symm_apply_apply]
  have hliftedq : lifted ≫ q = curve := by
    rw [← affinePointEquiv_comp, hgP, Equiv.apply_symm_apply]
  have hgq : g ≫ q = x := by
    change mapPoints (polynomialEvaluate R 1) (lifted ≫ q) = x
    rw [hliftedq, hcurve1]
  refine ⟨g, ⟨lifted, ?_, ?_⟩, ?_, hxfix⟩
  · apply (affinePointEquiv d (laurentAlgebra R)).symm.injective
    rw [pointCoordinates_map, Equiv.symm_apply_apply]
    apply AlgHom.ext
    intro z
    refine graded_induction V (fun z ↦
      ((polynomialToLaurent R).hom.comp gP) z =
        (affinePointEquiv d (laurentAlgebra R)).symm (orbit c g) z) z
        ?_ (by simp) (fun y w hy hw ↦ by simp only [map_add, hy, hw])
    intro n y hy
    have hp : Polynomial.toFinsuppIsoAlg k (gP y) ∈ polynomialGrades k n := by
      simpa only [gP, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
        using hgg n y hy
    change (gP y).toLaurent = _
    rw [toLaurent_of_polynomialGrade hp]
    have H := laurentAction_onWeight d bT g hy
    rw [lift_conjugation_smul] at H
    change (affinePointEquiv d (laurentAlgebra R)).symm (orbit c g) y = _ at H
    rw [H, show (affinePointEquiv d R).symm g = (polynomialEvaluate R 1).hom.comp gP from
      (pointCoordinates_map d (polynomialEvaluate R 1) lifted).trans
        (congrArg ((polynomialEvaluate R 1).hom.comp ·) (Equiv.symm_apply_apply _ _))]
    rfl
  · apply (affinePointEquiv d R).symm.injective
    rw [pointCoordinates_map, Equiv.symm_apply_apply]
    apply AlgHom.ext
    intro z
    change (gP z).eval 0 = ε z
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hg₀ z
  · rw [← hgq]
    let := a
    rw [orbitMap_comp]
    change lift g x₀ ≫ a.smul = lift g (toUnit _ ≫ (groundPointIso k).hom ≫ x₀) ≫ a.smul
    exact congrArg (fun p : Points X (groundField k) ↦ lift g p ≫ a.smul) (groundPoint_const x₀).symm

/-- Conjugate a cocharacter by a rational group element. -/
private def conjugateCocharacter (c : Cocharacter G) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    Cocharacter G := by
  let T := (Gm k).X
  let f : T ⟶ G.X := (toUnit T ≫ g) * c.hom.hom * (toUnit T ≫ g)⁻¹
  have comp {D : SchemeOver k} (s : D ⟶ T) :
      s ≫ f = (toUnit D ≫ g) * (s ≫ c.hom.hom) * (toUnit D ≫ g)⁻¹ := by
    simp only [f, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]
  refine Grp.homMk'' f ?_ ?_
  · rw [comp, IsMonHom.one_hom, MonObj.one_eq_one, mul_one, mul_inv_cancel]
  · let l := fst T T
    let r := snd T T
    let d := toUnit (T ⊗ T) ≫ g
    have hm : l * r = μ[T] := by
      change lift (fst T T) (snd T T) ≫ μ[T] = _
      rw [lift_fst_snd, Category.id_comp]
    calc
      μ[T] ≫ f = d * ((l ≫ c.hom.hom) * (r ≫ c.hom.hom)) * d⁻¹ := by
        rw [← hm, comp (l * r), MonObj.mul_comp]
      _ = (l ≫ f) * (r ≫ f) := by
        rw [comp l, comp r]
        change d * ((l ≫ c.hom.hom) * (r ≫ c.hom.hom)) * d⁻¹ =
          (d * (l ≫ c.hom.hom) * d⁻¹) * (d * (r ≫ c.hom.hom) * d⁻¹)
        group
      _ = (f ⊗ₘ f) ≫ μ[G.X] :=
        congrArg (· ≫ μ[G.X]) (lift_fst_comp_snd_comp f f)

/-- The scheme image of a nontrivial cocharacter is split of dimension one.
The character lattice of the image is a nonzero subgroup of the integer lattice. -/
private theorem split_cocharacter_image (P : AffineAlgebraicGroup k) (c : Cocharacter P.val)
    (hc : c.hom.hom ≠ 1) :
    ∃ (S : ClosedSubgroup P.val) (p : Cocharacter S.group),
      Nonempty (S.group ≅ Gm k) ∧ Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      p ≫ S.inclusion = c := by
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  let : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := z.symm.toMonoidHom) z.symm.surjective
  obtain ⟨I, p, i, ⟨hpi, hflat, hsurj, _, _, hclosed⟩, _, _⟩ :=
    schemeImageFactorization (diagonalGroup k IntegerCharacters.{u}) P c
  obtain ⟨N, ⟨e, he⟩, _⟩ :=
    (DiagonalizableGroups.diagonalFaithfullyFlatQuotients k IntegerCharacters.{u}
      ⟨I.val, I.property.1⟩ p).mp ⟨hflat, hsurj⟩
  have hN : Nontrivial N := by
    apply not_subsingleton_iff_nontrivial.mp
    intro h
    let R := CommAlgCat.of k (MonoidAlgebra k IntegerCharacters.{u})
    have : Subsingleton (N →* Rˣ) :=
      ⟨fun f g ↦ MonoidHom.ext fun n ↦ by rw [Subsingleton.elim n 1, map_one, map_one]⟩
    let E : GroupPoints (specGroup (groupAlgebra k N)) R ≃* (N →* Rˣ) :=
      ((DiagonalizableGroups.groupAlgebraPointsIso k N).app R).groupIsoToMulEquiv
    have hE : Subsingleton (GroupPoints (specGroup (groupAlgebra k N)) R) :=
      E.injective.subsingleton
    have hz : (Specs.DiagonalizableGroups.diagonalRestriction k N).hom.hom =
        (1 : GroupPoints (specGroup (groupAlgebra k N)) R) :=
      hE.elim _ _
    apply hc
    rw [← hpi, ← he]
    change (Specs.DiagonalizableGroups.diagonalRestriction k N).hom.hom ≫
      e.hom.hom.hom ≫ i.hom.hom = _
    simp only [hz, MonObj.one_comp]
  let : Nontrivial N := hN
  let : IsCyclic IntegerCharacters.{u} := z.isCyclic.mpr inferInstance
  let : Infinite IntegerCharacters.{u} := Infinite.of_injective z.symm z.symm.injective
  let : IsCyclic N := Subgroup.isCyclic N
  let equ := z.trans (intCyclicMulEquiv (G := N))
  let algebraIso :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k equ)
  let torusIso : specGroup (groupAlgebra k N) ≅ Gm k :=
    (hopfSpec (CommRingCat.of k)).mapIso algebraIso.op
  exact ⟨⟨I.val, i, hclosed⟩, p, ⟨e.symm ≪≫ torusIso⟩, hflat, hsurj, hpi⟩

private theorem hasConjugateSplitTorus (P : AffineAlgebraicGroup k) (a : ModObj P.val.X X)
    (c : Cocharacter P.val) (g : GroupPoints P.val (groundField k))
    (x x₀ : Points X (groundField k)) (hg : lift g x₀ ≫ a.smul = x)
    (hx₀ : Stabilizes a.smul ((groundPointIso k).hom ≫ x₀) c.hom.hom)
    (hc : c.hom.hom ≠ toUnit _ ≫ η[P.val.X]) : HasConjugateSplitTorus a c g x := by
  let := a
  let g' := (groundPointIso k).hom ≫ g
  let c' := conjugateCocharacter c g'
  let u : (Gm k).X ⟶ P.val.X := toUnit _ ≫ g'
  have hc' : c'.hom.hom = u * c.hom.hom * u⁻¹ := rfl
  have hnt : c'.hom.hom ≠ 1 := by
    intro he
    apply hc
    change c.hom.hom = 1
    calc
      c.hom.hom = u⁻¹ * (u * c.hom.hom * u⁻¹) * u := by group
      _ = 1 := by rw [← hc', he]; simp
  obtain ⟨S, p, hS, hpflat, hpsurj, hf⟩ := split_cocharacter_image P c' hnt
  let y := (groundPointIso k).hom ≫ x
  let y₀ := (groundPointIso k).hom ≫ x₀
  have hy : toUnit (Gm k).X ≫ y = u • (toUnit (Gm k).X ≫ y₀) := by
    simpa only [Hom.smul_def, u, g', y, y₀, Category.assoc, comp_lift_assoc] using
      congrArg ((toUnit (Gm k).X ≫ (groundPointIso k).hom) ≫ ·) hg.symm
  have hcStab : Stabilizes a.smul y c'.hom.hom := by
    change c'.hom.hom • (toUnit (Gm k).X ≫ y) = toUnit (Gm k).X ≫ y
    have hfix : c.hom.hom • (toUnit (Gm k).X ≫ y₀) = toUnit (Gm k).X ≫ y₀ := hx₀
    rw [hc', hy, mul_smul, mul_smul, inv_smul_smul, hfix]
  have hSStab : Stabilizes a.smul y S.inclusion.hom.hom := by
    let := hpflat
    let := hpsurj
    have hEpi : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
    have : Epi p.hom.hom := (Over.forget _).epi_of_epi_map hEpi
    apply (cancel_epi p.hom.hom).mp
    have hcomp : p.hom.hom ≫ S.inclusion.hom.hom = c'.hom.hom :=
      congrArg (fun h : (Gm k) ⟶ P.val ↦ h.hom.hom) hf
    simpa only [Stabilizes, Category.assoc, comp_lift_assoc, comp_toUnit_assoc, hcomp] using hcStab
  refine ⟨S, p, hS, hpsurj, ?_, fun T s ↦ stabilizes_comp a y hSStab s⟩
  rw [hf, hc']

/-- Rational contraction on the given affine smooth homogeneous quotient. -/
theorem quotientContractsRationally :
    Specs.RationalContraction.QuotientContractsRationally.{u} := by
  intro k _ P H Q V a b j _ hAff hSmooth hClosed hEq hProj
  let y := η[P.val.X] ≫ Q.projection
  have hq : Q.projection = Specs.SmoothOrbit.orbitMap b y := by
    let := hClosed
    let : Mono j := Over.mono_of_mono_left _
    apply (cancel_mono j).mp
    calc
      Q.projection ≫ j = Specs.SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j) := hProj
      _ = Specs.SmoothOrbit.orbitMap a (y ≫ j) :=
        congrArg (Specs.SmoothOrbit.orbitMap a) (Category.assoc _ _ _).symm
      _ = Specs.SmoothOrbit.orbitMap b y ≫ j := (orbitMap_equivariant b a j y hEq).symm
  have hs : ∀ x : 𝟙_ (SchemeOver k) ⟶ Q.scheme, Smooth (Specs.SmoothOrbit.orbitMap b x).left := by
    intro x
    apply smooth_orbitMap_of_surjective b P.property.1 hAff y x
    · rw [← hq]
      exact hSmooth
    · rw [← hq]
      exact Q.surjective
  intro c x x₀ hx
  obtain ⟨g, hg, hgx, hx₀⟩ :=
    rational_lift_of_smooth_orbitMap P.property.1 hAff b hs c x x₀ hx
  exact ⟨g, hg, hgx, hasConjugateSplitTorus P b c g x x₀ hgx hx₀⟩

/-- The closed homogeneous orbit has rational contraction for every cocharacter. -/
theorem rationalContraction : Specs.RationalContraction.RationalContraction.{u} := by
  intro k _ p _ _ m P hP H hH
  obtain ⟨Q, I, hI, dI, ρ, a, b, j, hAff, hTor, hSmooth, hClosed, hAction, hEq, hProj, hStab, _⟩ :=
    ClosedHomogeneousOrbits.closedHomogeneousOrbit k p m P hP H hH
  exact ⟨Q, I, hI, dI, ρ, a, b, j, hAff, hTor, hSmooth, hClosed, hAction, hEq, hProj, hStab,
    quotientContractsRationally P Q a b j hH hAff hSmooth hClosed hEq hProj⟩

end
end LinearAlgebraicGroups.Arithmetic.RationalContraction
