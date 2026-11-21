import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Naturality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.DirectedColimits

namespace AdvCommAlg.Differentials

open Specs.AdvCommAlg.Differentials (RingColimitPresentation)
open scoped TensorProduct
noncomputable section
universe ui ua ub uA uB un

namespace RingColimitPresentation
variable {ι : Type ui} [Preorder ι] [IsDirectedOrder ι]
  {R : ι → Type ua} [∀ i, CommRing (R i)]
  {f : ∀ i j, i ≤ j → R i →+* R j} [sys : DirectedSystem R (f · · ·)]
  {T : Type uA} [CommRing T] {inc : ∀ i, R i →+* T}
  (h : RingColimitPresentation R f T inc)

include h sys

/-- Equality of representatives from different stages is witnessed at a common stage. -/
theorem common {i j} {x : R i} {y : R j} (eq : inc i x = inc j y) :
    ∃ (k : ι) (hi : i ≤ k) (hj : j ≤ k), f i k hi x = f j k hj y := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have eq' : inc k (f i k hik x) = inc k (f j k hjk y) := by
    rw [h.cocone, h.cocone, eq]
  obtain ⟨l, hkl, he⟩ := h.eventually_equal k _ _ eq'
  exact ⟨l, hik.trans hkl, hjk.trans hkl, by
    simpa only [DirectedSystem.map_map' f] using he⟩

omit sys in
/-- Two elements can be represented at one common stage. -/
theorem representatives₂ (x y : T) :
    ∃ (i : ι) (a b : R i), inc i a = x ∧ inc i b = y := by
  obtain ⟨i, a, ha⟩ := h.representative x
  obtain ⟨j, b, hb⟩ := h.representative y
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨k, f i k hik a, f j k hjk b,
    (h.cocone _ _ _ _).trans ha, (h.cocone _ _ _ _).trans hb⟩

/-- These ring hypotheses describe the actual ring colimit. -/
def ringEquiv [Nonempty ι] : _root_.DirectLimit R f ≃+* T :=
  RingEquiv.ofBijective (_root_.DirectLimit.Ring.lift R f T inc h.cocone) ⟨by
    apply _root_.DirectLimit.induction₂
    intro i x y he
    obtain ⟨j, hij, he⟩ := h.eventually_equal i x y he
    exact Quotient.sound ⟨j, hij, hij, he⟩,
    fun x => by
      obtain ⟨i, y, hy⟩ := h.representative x
      exact ⟨⟦⟨i, y⟩⟧, hy⟩⟩

omit h in
/-- The presentation condition is equivalent to being the standard directed
ring colimit, by an isomorphism respecting every structure map. Thus the
representative hypotheses impose no restriction on the colimit model. -/
theorem presentation_iff_ringEquiv [Nonempty ι] :
    RingColimitPresentation R f T inc ↔
      ∃ e : _root_.DirectLimit R f ≃+* T,
        ∀ i x, e (_root_.DirectLimit.Ring.of R f i x) = inc i x := by
  constructor
  · intro hc
    exact ⟨ringEquiv hc, fun _ _ => rfl⟩
  · rintro ⟨e, he⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij x
      rw [← he, _root_.DirectLimit.Ring.of_f, he]
    · intro x
      obtain ⟨z, rfl⟩ := e.surjective x
      obtain ⟨i, y, rfl⟩ := _root_.DirectLimit.exists_eq_mk f z
      exact ⟨i, y, (he i y).symm⟩
    · intro i x y hxy
      have heq : (_root_.DirectLimit.Ring.of R f i x) =
          _root_.DirectLimit.Ring.of R f i y := e.injective (by rw [he, he, hxy])
      obtain ⟨j, hij, hij', hj⟩ := Quotient.eq.mp heq
      exact ⟨j, hij, hj⟩

variable {N : Type un}

/-- Glue a compatible family of functions on stage representatives. -/
def glueFunction (g : ∀ i, R i → N)
    (_compat : ∀ i j h x, g j (f i j h x) = g i x) (x : T) : N :=
  g (h.representative x).choose ((h.representative x).choose_spec.choose)

@[simp] theorem glueFunction_inc (g : ∀ i, R i → N)
    (compat : ∀ i j h x, g j (f i j h x) = g i x) (i : ι) (x : R i) :
    glueFunction h g compat (inc i x) = g i x := by
  unfold glueFunction
  obtain ⟨k, hk, hi, he⟩ := common h (h.representative (inc i x)).choose_spec.choose_spec
  rw [← compat _ _ hk, he, compat]


include h in
lemma glueFunction_add [AddCommGroup N] (g : ∀ i, R i → N)
    (compat : ∀ i j h x, g j (f i j h x) = g i x)
    (hadd : ∀ i x y, g i (x + y) = g i x + g i y) (x y : T) :
    glueFunction h g compat (x + y) =
      glueFunction h g compat x + glueFunction h g compat y := by
  obtain ⟨i, a, b, rfl, rfl⟩ := representatives₂ h x y
  rw [← map_add, glueFunction_inc, glueFunction_inc, glueFunction_inc, hadd]

include h in
lemma glueFunction_leibniz [AddCommGroup N] [Module T N] (g : ∀ i, R i → N)
    (compat : ∀ i j h x, g j (f i j h x) = g i x)
    (hmul : ∀ i x y, g i (x * y) = inc i x • g i y + inc i y • g i x) (x y : T) :
    glueFunction h g compat (x * y) =
      x • glueFunction h g compat y + y • glueFunction h g compat x := by
  obtain ⟨i, a, b, rfl, rfl⟩ := representatives₂ h x y
  rw [← map_mul, glueFunction_inc, glueFunction_inc, glueFunction_inc, hmul]


end RingColimitPresentation

/-- Extend a semilinear map to the scalar extension. -/
def extendScalars {R : Type ua} {S : Type ub} [CommRing R] [CommRing S]
    [Algebra R S] {M : Type uA} {N : Type uB}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) : S ⊗[R] M →ₗ[S] N := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact LinearMap.liftBaseChange S
    { toFun := f, map_add' := f.map_add, map_smul' := f.map_smul' }

@[simp] theorem extendScalars_tmul {R : Type ua} {S : Type ub} [CommRing R] [CommRing S]
    [Algebra R S] {M : Type uA} {N : Type uB}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) (s : S) (m : M) :
    extendScalars f (s ⊗ₜ m) = s • f m := rfl

/-- The unit map of scalar extension, as a semilinear map. -/
def unitTensor {R : Type ua} (S : Type ub) [CommRing R] [CommRing S]
    [Algebra R S] (M : Type uA) [AddCommGroup M] [Module R M] :
    M →ₛₗ[algebraMap R S] S ⊗[R] M where
  toFun m := 1 ⊗ₜ m
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' r m := by
    rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S]


/-- Functoriality expressed without a restricted-scalar instance in the type. -/
def differentialSemilinear {A : Type ua} {B : Type ub} {A' : Type uA} {B' : Type uB}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g) :
    KaehlerDifferential A B →ₛₗ[f] KaehlerDifferential A' B' := by
  letI : Algebra B B' := f.toAlgebra
  exact
    { toFun := algebraDifferentialMap g f h
      map_add' := map_add _
      map_smul' := algebraDifferentialMap_smul g f h }

@[simp] theorem differentialSemilinear_D
    {A : Type ua} {B : Type ub} {A' : Type uA} {B' : Type uB}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g) (b : B) :
    differentialSemilinear g f h (KaehlerDifferential.D A B b) =
      KaehlerDifferential.D A' B' (f b) :=
  algebraDifferentialMap_apply g f h b

/-- Scalar-extended transition for one commuting square in a cocone. -/
def tensorDifferentialMap
    {A : Type ua} {B : Type ub} {A' : Type uA} {B' : Type uB}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (C : Type un) [CommRing C]
    [Algebra B C] [Algebra B' C]
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g)
    (hc : (algebraMap B' C).comp f = algebraMap B C) :
    C ⊗[B] KaehlerDifferential A B →ₗ[C] C ⊗[B'] KaehlerDifferential A' B' :=
  extendScalars
    { toFun := fun x => unitTensor C _ (differentialSemilinear g f h x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun b x => by
        simp only [map_smulₛₗ]
        rw [show algebraMap B' C (f b) = algebraMap B C b from
          congrArg (fun p : B →+* C => p b) hc] }

@[simp] theorem tensorDifferentialMap_tmul_D
    {A : Type ua} {B : Type ub} {A' : Type uA} {B' : Type uB}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] (C : Type un) [CommRing C]
    [Algebra B C] [Algebra B' C]
    (g : A →+* A') (f : B →+* B')
    (h : f.comp (algebraMap A B) = (algebraMap A' B').comp g)
    (hc : (algebraMap B' C).comp f = algebraMap B C) (c : C) (b : B) :
    tensorDifferentialMap C g f h hc (c ⊗ₜ KaehlerDifferential.D A B b) =
      c ⊗ₜ KaehlerDifferential.D A' B' (f b) := by
  simp only [tensorDifferentialMap, extendScalars_tmul, differentialSemilinear_D,
    unitTensor, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Extended differentials generate a scalar extension of a differential module. -/
theorem ext_tensor_differentials
    {A : Type ua} {B : Type ub} [CommRing A] [CommRing B] [Algebra A B]
    {C : Type uA} [CommRing C] [Algebra B C]
    {N : Type uB} [AddCommGroup N] [Module C N]
    {f g : C ⊗[B] KaehlerDifferential A B →ₗ[C] N}
    (h : ∀ c b, f (c ⊗ₜ KaehlerDifferential.D A B b) =
      g (c ⊗ₜ KaehlerDifferential.D A B b)) : f = g := by
  let : Module B N := Module.compHom N (algebraMap B C)
  let : IsScalarTower B C N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  revert c
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; exact fun c => h c b
  | zero => intro c; simp
  | add x y hx hy ex ey => intro c; simp only [TensorProduct.tmul_add, map_add, ex, ey]
  | smul b x hx ex => intro c; rw [← TensorProduct.smul_tmul, ex]



/-- Differentials commute with directed colimits, with both rings varying. -/
theorem directed_colimits :
    Specs.AdvCommAlg.Differentials.directedColimits.{ui,ua,ub,uA,uB} := by
  intro ι _ _ _ Ai Bi _ _ _ A B _ _ _ _ _ fa fb _ _ square hA hB limitSquare
  classical
  let T := fun i => B ⊗[Bi i] KaehlerDifferential (Ai i) (Bi i)
  let t : ∀ i j, i ≤ j → T i →ₗ[B] T j := fun i j h =>
    tensorDifferentialMap B (fa i j h) (fb i j h) (square i j h)
      (by ext b; exact hB.cocone i j h b)
  have ht : ∀ i j h (c : B) (b : Bi i),
      t i j h (c ⊗ₜ KaehlerDifferential.D (Ai i) (Bi i) b) =
        c ⊗ₜ KaehlerDifferential.D (Ai j) (Bi j) (fb i j h b) := by
    intro i j h c b
    exact tensorDifferentialMap_tmul_D _ _ _ _ _ _ _
  have htself : ∀ i, t i i le_rfl = LinearMap.id := by
    intro i
    apply ext_tensor_differentials
    intro c b
    rw [ht, DirectedSystem.map_self' fb]
    rfl
  have htcomp : ∀ i j k (h : i ≤ j) (h' : j ≤ k),
      (t j k h').comp (t i j h) = t i k (h.trans h') := by
    intro i j k h h'
    apply ext_tensor_differentials
    intro c b
    simp only [LinearMap.comp_apply, ht, DirectedSystem.map_map' fb]
  refine ⟨t, ht, htself, htcomp, ?_⟩
  let L := Module.DirectLimit T t
  let ofL := Module.DirectLimit.of B ι T t
  let q : ∀ i, T i →ₗ[B] KaehlerDifferential A B := fun i =>
    extendScalars (differentialSemilinear (algebraMap (Ai i) A)
      (algebraMap (Bi i) B) (limitSquare i))
  have hq : ∀ i (c : B) (b : Bi i),
      q i (c ⊗ₜ KaehlerDifferential.D (Ai i) (Bi i) b) =
        c • KaehlerDifferential.D A B (algebraMap (Bi i) B b) := by
    intro i c b
    change c • differentialSemilinear (algebraMap (Ai i) A) (algebraMap (Bi i) B)
      (limitSquare i) (KaehlerDifferential.D (Ai i) (Bi i) b) = _
    rw [differentialSemilinear_D]
  have qcompat : ∀ i j h x, q j (t i j h x) = q i x := by
    intro i j h
    have he : (q j).comp (t i j h) = q i := by
      apply ext_tensor_differentials
      intro c b
      simp only [LinearMap.comp_apply, ht, hq, hB.cocone]
    exact fun x => congrArg (fun f => f x) he
  let F : L →ₗ[B] KaehlerDifferential A B := Module.DirectLimit.lift B ι T t q qcompat
  have hF : ∀ i x, F (ofL i x) = q i x := fun _ _ => Module.DirectLimit.lift_of _ _ _
  let d : ∀ i, Bi i → L := fun i b =>
    ofL i (unitTensor B _ (KaehlerDifferential.D (Ai i) (Bi i) b))
  have dcompat : ∀ i j h b, d j (fb i j h b) = d i b := by
    intro i j h b
    change ofL j (1 ⊗ₜ KaehlerDifferential.D (Ai j) (Bi j) (fb i j h b)) =
      ofL i (1 ⊗ₜ KaehlerDifferential.D (Ai i) (Bi i) b)
    rw [← ht i j h 1 b]
    exact Module.DirectLimit.of_f
  have dadd : ∀ i x y, d i (x + y) = d i x + d i y := by
    intro i x y
    simp only [d, map_add]
  have dmul : ∀ i x y, d i (x * y) =
      algebraMap (Bi i) B x • d i y + algebraMap (Bi i) B y • d i x := by
    intro i x y
    simp only [d, Derivation.leibniz, map_add, map_smulₛₗ, RingHom.id_apply]
  have dbase : ∀ i a, d i (algebraMap (Ai i) (Bi i) a) = 0 := by
    intro i a
    simp only [d, Derivation.map_algebraMap, map_zero]
  let G : B → L := RingColimitPresentation.glueFunction hB d dcompat
  have Gadd : ∀ x y, G (x + y) = G x + G y :=
    RingColimitPresentation.glueFunction_add hB d dcompat dadd
  have Gmul : ∀ x y, G (x * y) = x • G y + y • G x :=
    RingColimitPresentation.glueFunction_leibniz hB d dcompat dmul
  have Gbase : ∀ a : A, G (algebraMap A B a) = 0 := by
    intro a
    obtain ⟨i, a, rfl⟩ := hA.representative a
    have he := congrArg (fun f : Ai i →+* B => f a) (limitSquare i)
    change algebraMap (Bi i) B (algebraMap (Ai i) (Bi i) a) =
      algebraMap A B (algebraMap (Ai i) A a) at he
    rw [← he]
    exact (RingColimitPresentation.glueFunction_inc hB d dcompat i _).trans (dbase i a)
  let : Module A L := Module.compHom L (algebraMap A B)
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨δ, hδ, _⟩ := (additive_characterization (A := A) (B := B) (M := L) G).mpr
    ⟨Gadd, Gmul, Gbase⟩
  let inv := Derivation.liftKaehlerDifferential (R := A) (S := B) (M := L) δ
  have hinv : ∀ i (b : Bi i),
      inv (KaehlerDifferential.D A B (algebraMap (Bi i) B b)) =
        ofL i (1 ⊗ₜ KaehlerDifferential.D (Ai i) (Bi i) b) := by
    intro i b
    change Derivation.liftKaehlerDifferential (R := A) (S := B) (M := L) δ _ = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rw [show δ (algebraMap (Bi i) B b) = G (algebraMap (Bi i) B b) from
      congrFun hδ _]
    exact RingColimitPresentation.glueFunction_inc hB d dcompat i b
  have hinvF : inv.comp F = LinearMap.id := by
    apply Module.DirectLimit.hom_ext
    intro i
    apply ext_tensor_differentials (A := Ai i) (B := Bi i) (C := B) (N := L)
    intro c b
    change inv (F (ofL i (c ⊗ₜ KaehlerDifferential.D (Ai i) (Bi i) b))) =
      ofL i (c ⊗ₜ KaehlerDifferential.D (Ai i) (Bi i) b)
    rw [hF, hq, map_smul, hinv]
    rw [← map_smul, TensorProduct.smul_tmul']
    simp only [smul_eq_mul, mul_one]
  have hFinv : F.comp inv = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro b
    obtain ⟨i, b, rfl⟩ := hB.representative b
    change F (inv (KaehlerDifferential.D A B (algebraMap (Bi i) B b))) = _
    rw [hinv, hF, hq, one_smul]
    rfl
  let e : L ≃ₗ[B] KaehlerDifferential A B :=
    { F with
      invFun := inv
      left_inv := fun x => congrArg (fun f : L →ₗ[B] L => f x) hinvF
      right_inv := fun x => congrArg
        (fun f : KaehlerDifferential A B →ₗ[B] KaehlerDifferential A B => f x) hFinv }
  refine ⟨e, ?_⟩
  intro i c b
  exact (hF i _).trans (hq i c b)


end
end AdvCommAlg.Differentials
