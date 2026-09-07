import InformationTheoreticCrypto.Section31

/-!
# Native PRP/PRF switching proof over the Section 3.1 semantics

Unlike `Section31Switching.lean`, this module does not import or translate the
separate `PRPPRFSwitching` runner.  Every public statement and every oracle
execution below uses the definitions of `Section31.lean` directly.  Lazy
tables are private proof state used to analyze the two Section 3.1 random
systems.
-/

namespace InformationTheoreticSecurity.Section31.NativeSwitching

open InformationTheoreticSecurity.Section31

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The Section 3.1 random stateless system induced by a uniform function. -/
noncomputable def randomFunctionSystem : RandomSystem X X :=
  randomStatelessSystem (PMF.uniformOfFintype (X → X))

/-- The Section 3.1 random stateless system induced by a uniform permutation. -/
noncomputable def randomPermutationSystem : RandomSystem X X :=
  randomStatelessSystem
    ((PMF.uniformOfFintype (Equiv.Perm X)).map
      (fun p : Equiv.Perm X => (p : X → X)))

/-- Private state of the lazy proof implementation. -/
structure OracleState (X : Type u) [Fintype X] [DecidableEq X] where
  table : X → Option X
  usedOutputs : Finset X

def initialState (X : Type u) [Fintype X] [DecidableEq X] : OracleState X where
  table := fun _ => none
  usedOutputs := ∅

def store (s : OracleState X) (x y : X) : OracleState X where
  table := fun z => if z = x then some y else s.table z
  usedOutputs := insert y s.usedOutputs

@[simp] theorem initial_lookup (x : X) : (initialState X).table x = none := rfl
@[simp] theorem initial_used : (initialState X).usedOutputs = ∅ := rfl
@[simp] theorem store_lookup_same (s : OracleState X) (x y : X) :
    (store s x y).table x = some y := by simp [store]
theorem store_lookup_of_ne (s : OracleState X) {x z y : X} (h : z ≠ x) :
    (store s x y).table z = s.table z := by simp [store, h]
@[simp] theorem store_used (s : OracleState X) (x y : X) :
    (store s x y).usedOutputs = insert y s.usedOutputs := rfl

def CoversTable (s : OracleState X) : Prop :=
  ∀ ⦃x y⦄, s.table x = some y → y ∈ s.usedOutputs

def ExactUsed (s : OracleState X) : Prop :=
  ∀ y, y ∈ s.usedOutputs ↔ ∃ x, s.table x = some y

def InjectiveTable (s : OracleState X) : Prop :=
  ∀ ⦃x₁ x₂ y⦄, s.table x₁ = some y → s.table x₂ = some y → x₁ = x₂

def availableOutputs (s : OracleState X) : Finset X :=
  Finset.univ \ s.usedOutputs

theorem mem_availableOutputs_iff (s : OracleState X) (y : X) :
    y ∈ availableOutputs s ↔ y ∉ s.usedOutputs := by
  simp [availableOutputs]

theorem availableOutputs_nonempty_of_card_lt (s : OracleState X)
    (h : s.usedOutputs.card < Fintype.card X) :
    (availableOutputs s).Nonempty := by
  rw [availableOutputs, Finset.sdiff_nonempty]
  intro hsub
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ] at this
  omega

theorem initial_covers : CoversTable (initialState X) := by simp [CoversTable]
theorem initial_exact : ExactUsed (initialState X) := by simp [ExactUsed]
theorem initial_injective : InjectiveTable (initialState X) := by
  intro x₁ x₂ y h
  simp at h

theorem store_covers (s : OracleState X) (x y : X) (hs : CoversTable s) :
    CoversTable (store s x y) := by
  intro z w hzw
  by_cases hzx : z = x
  · subst z
    simp only [store_lookup_same] at hzw
    cases hzw
    simp
  · rw [store_lookup_of_ne s hzx] at hzw
    exact Finset.mem_insert_of_mem (hs hzw)

theorem store_exact (s : OracleState X) (x y : X)
    (hx : s.table x = none) (hs : ExactUsed s) : ExactUsed (store s x y) := by
  intro w
  constructor
  · intro hw
    simp only [store_used, Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact ⟨x, store_lookup_same s x w⟩
    · obtain ⟨z, hz⟩ := (hs w).mp hw
      have hzx : z ≠ x := by
        intro h; subst z; rw [hx] at hz; contradiction
      exact ⟨z, by simpa only [store_lookup_of_ne s hzx] using hz⟩
  · rintro ⟨z, hz⟩
    by_cases hzx : z = x
    · subst z
      simp only [store_lookup_same] at hz
      cases hz
      simp
    · rw [store_lookup_of_ne s hzx] at hz
      exact Finset.mem_insert_of_mem ((hs w).mpr ⟨z, hz⟩)

theorem store_injective (s : OracleState X) (x y : X)
    (hs : InjectiveTable s) (hx : s.table x = none)
    (hy : y ∉ s.usedOutputs) (hc : CoversTable s) :
    InjectiveTable (store s x y) := by
  intro z₁ z₂ w h₁ h₂
  by_cases h₁x : z₁ = x
  · subst z₁
    simp only [store_lookup_same] at h₁
    cases h₁
    by_cases h₂x : z₂ = x
    · exact h₂x.symm
    · rw [store_lookup_of_ne s h₂x] at h₂
      exact False.elim (hy (hc h₂))
  · rw [store_lookup_of_ne s h₁x] at h₁
    by_cases h₂x : z₂ = x
    · subst z₂
      simp only [store_lookup_same] at h₂
      cases h₂
      exact False.elim (hy (hc h₁))
    · rw [store_lookup_of_ne s h₂x] at h₂
      exact hs h₁ h₂

/-- One native lazy step. -/
abbrev Step := X → OracleState X → PMF (X × OracleState X)

noncomputable def rfStep : Step (X := X) := fun x s =>
  match s.table x with
  | some y => PMF.pure (y, s)
  | none => (PMF.uniformOfFintype X).map fun y => (y, store s x y)

noncomputable def rpStep : Step (X := X) := fun x s =>
  match s.table x with
  | some y => PMF.pure (y, s)
  | none =>
      if h : (availableOutputs s).Nonempty then
        (PMF.uniformOfFinset (availableOutputs s) h).map fun y =>
          (y, store s x y)
      else PMF.pure (Classical.choice inferInstance, s)

/-- A lazy execution driven directly by a Section 3.1 `QueryFunction`. -/
noncomputable def runLazy (Q : QueryFunction X X) (step : Step (X := X)) :
    ℕ → Transcript X X → OracleState X →
      PMF (Transcript X X × OracleState X)
  | 0, tr, s => PMF.pure (tr, s)
  | fuel + 1, tr, s =>
      match Q.next (responses tr) with
      | none => PMF.pure (tr, s)
      | some x =>
          (step x s).bind fun ys =>
            runLazy Q step fuel (tr ++ [(x, ys.1)]) ys.2

noncomputable def lazyRF (Q : QueryFunction X X) (q : ℕ) :=
  runLazy Q rfStep q [] (initialState X)

noncomputable def lazyRP (Q : QueryFunction X X) (q : ℕ) :=
  runLazy Q rpStep q [] (initialState X)

noncomputable def visible
    (p : PMF (Transcript X X × OracleState X)) : PMF (Transcript X X) :=
  p.map Prod.fst

/-! ## Total completions of the native lazy function table -/

def FunctionCompatible (s : OracleState X) (f : X → X) : Prop :=
  ∀ x y, s.table x = some y → f x = y

noncomputable instance (s : OracleState X) :
    DecidablePred (FunctionCompatible s) := fun _ => Classical.propDecidable _

noncomputable def functionCompletions (s : OracleState X) : Finset (X → X) :=
  Finset.univ.filter (FunctionCompatible s)

theorem mem_functionCompletions_iff (s : OracleState X) (f : X → X) :
    f ∈ functionCompletions s ↔ FunctionCompatible s f := by
  simp [functionCompletions]

@[simp] theorem functionCompletions_initial :
    functionCompletions (initialState X) = Finset.univ := by
  ext f
  simp [functionCompletions, FunctionCompatible]

theorem functionCompatible_store_iff (s : OracleState X) (x y : X)
    (hx : s.table x = none) (f : X → X) :
    FunctionCompatible (store s x y) f ↔ FunctionCompatible s f ∧ f x = y := by
  constructor
  · intro h
    refine ⟨?_, h x y (store_lookup_same s x y)⟩
    intro z w hzw
    have hzx : z ≠ x := by
      intro hz; subst z; rw [hx] at hzw; contradiction
    exact h z w (by simpa only [store_lookup_of_ne s hzx] using hzw)
  · rintro ⟨hs, hxy⟩ z w hzw
    by_cases hzx : z = x
    · subst z
      simp only [store_lookup_same] at hzw
      cases hzw
      exact hxy
    · rw [store_lookup_of_ne s hzx] at hzw
      exact hs z w hzw

noncomputable def functionCompletionFiber (s : OracleState X) (x y : X) :
    Finset (X → X) :=
  (functionCompletions s).filter fun f => f x = y

theorem mem_functionCompletionFiber_iff (s : OracleState X) (x y : X)
    (f : X → X) :
    f ∈ functionCompletionFiber s x y ↔
      f ∈ functionCompletions s ∧ f x = y := by
  simp [functionCompletionFiber]

theorem functionCompletions_store_eq_fiber (s : OracleState X) (x y : X)
    (hx : s.table x = none) :
    functionCompletions (store s x y) = functionCompletionFiber s x y := by
  ext f
  simp [mem_functionCompletions_iff, mem_functionCompletionFiber_iff,
    functionCompatible_store_iff s x y hx f]

theorem functionCompatible_update_fresh (s : OracleState X) (x y : X)
    (hx : s.table x = none) {f : X → X} (hf : FunctionCompatible s f) :
    FunctionCompatible s (Function.update f x y) := by
  intro z w hzw
  have hzx : z ≠ x := by
    intro hz; subst z; rw [hx] at hzw; contradiction
  simp only [Function.update, hzx, ↓reduceIte]
  exact hf z w hzw

noncomputable def functionCompletionFiberEquiv (s : OracleState X)
    (x y₁ y₂ : X) (hx : s.table x = none) :
    {f // f ∈ functionCompletionFiber s x y₁} ≃
      {f // f ∈ functionCompletionFiber s x y₂} where
  toFun f := ⟨Function.update f.1 x y₂, by
    rw [mem_functionCompletionFiber_iff]
    have hf := (mem_functionCompletionFiber_iff s x y₁ f.1).mp f.2
    exact ⟨(mem_functionCompletions_iff s _).mpr
      (functionCompatible_update_fresh s x y₂ hx
        ((mem_functionCompletions_iff s _).mp hf.1)), by simp⟩⟩
  invFun f := ⟨Function.update f.1 x y₁, by
    rw [mem_functionCompletionFiber_iff]
    have hf := (mem_functionCompletionFiber_iff s x y₂ f.1).mp f.2
    exact ⟨(mem_functionCompletions_iff s _).mpr
      (functionCompatible_update_fresh s x y₁ hx
        ((mem_functionCompletions_iff s _).mp hf.1)), by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    by_cases hzx : z = x
    · subst z
      have hf := (mem_functionCompletionFiber_iff s x y₁ f.1).mp f.2
      simp [hf.2]
    · simp [Function.update, hzx]
  right_inv f := by
    apply Subtype.ext
    funext z
    by_cases hzx : z = x
    · subst z
      have hf := (mem_functionCompletionFiber_iff s x y₂ f.1).mp f.2
      simp [hf.2]
    · simp [Function.update, hzx]

theorem card_functionCompletionFiber_eq (s : OracleState X) (x y₁ y₂ : X)
    (hx : s.table x = none) :
    (functionCompletionFiber s x y₁).card =
      (functionCompletionFiber s x y₂).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (functionCompletionFiberEquiv s x y₁ y₂ hx)

theorem functionCompletions_nonempty (s : OracleState X) :
    (functionCompletions s).Nonempty := by
  let d : X := Classical.choice inferInstance
  let f : X → X := fun x => (s.table x).getD d
  refine ⟨f, (mem_functionCompletions_iff s f).mpr ?_⟩
  intro x y hxy
  simp [f, hxy]

theorem card_functionCompletions_eq_mul_fiber (s : OracleState X) (x y : X)
    (hx : s.table x = none) :
    (functionCompletions s).card =
      Fintype.card X * (functionCompletionFiber s x y).card := by
  classical
  calc
    (functionCompletions s).card =
        ∑ z ∈ (Finset.univ : Finset X),
          ((functionCompletions s).filter fun f => f x = z).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro f hf
      simp
    _ = ∑ z ∈ (Finset.univ : Finset X),
          (functionCompletionFiber s x z).card := by rfl
    _ = ∑ _z ∈ (Finset.univ : Finset X),
          (functionCompletionFiber s x y).card := by
      apply Finset.sum_congr rfl
      intro z hz
      exact card_functionCompletionFiber_eq s x z y hx
    _ = Fintype.card X * (functionCompletionFiber s x y).card := by simp

noncomputable def uniformFunctionCompletion (s : OracleState X) : PMF (X → X) :=
  PMF.uniformOfFinset (functionCompletions s) (functionCompletions_nonempty s)

@[simp] theorem uniformFunctionCompletion_initial :
    uniformFunctionCompletion (initialState X) = PMF.uniformOfFintype (X → X) := by
  simp [uniformFunctionCompletion, functionCompletions_initial,
    PMF.uniformOfFintype]

theorem uniformFunctionCompletion_fresh (s : OracleState X) (x : X)
    (hx : s.table x = none) :
    (PMF.uniformOfFintype X).bind
        (fun y => uniformFunctionCompletion (store s x y)) =
      uniformFunctionCompletion s := by
  apply PMF.ext
  intro f
  rw [PMF.bind_apply, tsum_fintype]
  simp only [uniformFunctionCompletion, PMF.uniformOfFintype_apply,
    PMF.uniformOfFinset_apply]
  by_cases hf : f ∈ functionCompletions s
  · have hmem : ∀ y : X,
        (f ∈ functionCompletions (store s x y)) ↔ f x = y := by
      intro y
      rw [functionCompletions_store_eq_fiber s x y hx,
        mem_functionCompletionFiber_iff]
      simp [hf]
    have hcard : ∀ y : X,
        (functionCompletions (store s x y)).card =
          (functionCompletionFiber s x (f x)).card := by
      intro y
      rw [functionCompletions_store_eq_fiber s x y hx]
      exact card_functionCompletionFiber_eq s x y (f x) hx
    simp_rw [hmem, hcard]
    simp only [hf, if_true]
    rw [Fintype.sum_eq_single (f x)]
    · simp only [↓reduceIte]
      rw [card_functionCompletions_eq_mul_fiber s x (f x) hx]
      push_cast
      rw [ENNReal.mul_inv (by left; simp) (by left; simp)]
    · intro y hne
      simp [hne, Ne.symm hne]
  · have hnone : ∀ y : X, f ∉ functionCompletions (store s x y) := by
      intro y hy
      apply hf
      rw [mem_functionCompletions_iff]
      exact ((functionCompatible_store_iff s x y hx f).mp
        ((mem_functionCompletions_iff _ _).mp hy)).1
    simp [hf, hnone]

theorem pmf_map_congr_support (p : PMF Α) (f g : Α → Β)
    (h : ∀ a, p a ≠ 0 → f a = g a) : p.map f = p.map g := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

/-- Native deferred decisions for the complete Section 3.1 interaction. -/
theorem completionInteraction_eq_lazyRF (Q : QueryFunction X X) (fuel : ℕ)
    (tr : Transcript X X) (s : OracleState X) :
    (uniformFunctionCompletion s).map
        (fun f => interact Q (statelessSystem f) fuel tr) =
      (runLazy Q rfStep fuel tr s).map Prod.fst := by
  induction fuel generalizing tr s with
  | zero =>
      rw [show (fun f : X → X => interact Q (statelessSystem f) 0 tr) =
        Function.const (X → X) tr by funext f; rfl, PMF.map_const]
      simp [runLazy, PMF.pure_map]
  | succ fuel ih =>
      cases hQ : Q.next (responses tr) with
      | none =>
          rw [show (fun f : X → X => interact Q (statelessSystem f) (fuel + 1) tr) =
            Function.const (X → X) tr by funext f; simp [interact, hQ], PMF.map_const]
          simp [runLazy, hQ, PMF.pure_map]
      | some x =>
          cases hx : s.table x with
          | some y =>
              have hpoint : ∀ f, uniformFunctionCompletion s f ≠ 0 →
                  interact Q (statelessSystem f) (fuel + 1) tr =
                    interact Q (statelessSystem f) fuel (tr ++ [(x, y)]) := by
                intro f hf
                have hfmem : f ∈ functionCompletions s := by
                  by_contra hn
                  exact hf (by simp [uniformFunctionCompletion,
                    PMF.uniformOfFinset_apply, hn])
                have hfx : f x = y :=
                  ((mem_functionCompletions_iff s f).mp hfmem) x y hx
                simp only [interact, hQ, statelessSystem]
                have hlast : NonemptyHistory.last
                    (NonemptyHistory.ofList (queries tr ++ [x]) (by simp)) = x := by
                  have hlist := NonemptyHistory.toList_ofList
                    (queries tr ++ [x]) (by simp)
                  unfold NonemptyHistory.last
                  simpa using congrArg
                    (fun zs => zs.getLast (by simpa using
                      (List.append_ne_nil_of_ne_nil_right (queries tr) (by simp : [x] ≠ []))))
                    hlist
                simp [hlast, hfx]
              rw [pmf_map_congr_support _ _ _ hpoint]
              rw [ih]
              simp [runLazy, hQ, rfStep, hx, PMF.pure_bind, PMF.map_comp]
          | none =>
              rw [← uniformFunctionCompletion_fresh s x hx, PMF.map_bind]
              have hbranch : ∀ y : X,
                  (uniformFunctionCompletion (store s x y)).map
                      (fun f => interact Q (statelessSystem f) (fuel + 1) tr) =
                    (uniformFunctionCompletion (store s x y)).map
                      (fun f => interact Q (statelessSystem f) fuel
                        (tr ++ [(x, y)])) := by
                intro y
                apply pmf_map_congr_support
                intro f hf
                have hfmem : f ∈ functionCompletions (store s x y) := by
                  by_contra hn
                  exact hf (by simp [uniformFunctionCompletion,
                    PMF.uniformOfFinset_apply, hn])
                have hfy : f x = y :=
                  ((functionCompatible_store_iff s x y hx f).mp
                    ((mem_functionCompletions_iff _ _).mp hfmem)).2
                simp only [interact, hQ, statelessSystem]
                have hlast : NonemptyHistory.last
                    (NonemptyHistory.ofList (queries tr ++ [x]) (by simp)) = x := by
                  unfold NonemptyHistory.last
                  simp only [NonemptyHistory.toList_ofList]
                  simp
                simp [hlast, hfy]
              simp_rw [hbranch]
              simp_rw [ih]
              simp [runLazy, hQ, rfStep, hx, PMF.map_bind, PMF.map_comp]

theorem transcriptDistribution_randomFunction_eq_lazy
    (q : ℕ) (Q : QueryFunction X X) :
    transcriptDistribution q Q (randomFunctionSystem (X := X)) =
      visible (lazyRF Q q) := by
  rw [transcriptDistribution, randomFunctionSystem, randomStatelessSystem,
    PMF.map_comp]
  change (PMF.uniformOfFintype (X → X)).map
      (fun f => interact Q (statelessSystem f) q []) = _
  rw [← uniformFunctionCompletion_initial]
  exact completionInteraction_eq_lazyRF Q q [] (initialState X)

/-! ## Total completions of the native lazy permutation table -/

def PermutationCompatible (s : OracleState X) (p : Equiv.Perm X) : Prop :=
  ∀ x y, s.table x = some y → p x = y

noncomputable instance (s : OracleState X) :
    DecidablePred (PermutationCompatible s) := fun _ => Classical.propDecidable _

noncomputable def permutationCompletions (s : OracleState X) :
    Finset (Equiv.Perm X) :=
  Finset.univ.filter (PermutationCompatible s)

theorem mem_permutationCompletions_iff (s : OracleState X) (p : Equiv.Perm X) :
    p ∈ permutationCompletions s ↔ PermutationCompatible s p := by
  simp [permutationCompletions]

@[simp] theorem permutationCompletions_initial :
    permutationCompletions (initialState X) = Finset.univ := by
  ext p
  simp [permutationCompletions, PermutationCompatible]

theorem permutationCompatible_store_iff (s : OracleState X) (x y : X)
    (hx : s.table x = none) (p : Equiv.Perm X) :
    PermutationCompatible (store s x y) p ↔
      PermutationCompatible s p ∧ p x = y := by
  constructor
  · intro h
    refine ⟨?_, h x y (store_lookup_same s x y)⟩
    intro z w hzw
    have hzx : z ≠ x := by
      intro hz; subst z; rw [hx] at hzw; contradiction
    exact h z w (by simpa only [store_lookup_of_ne s hzx] using hzw)
  · rintro ⟨hs, hxy⟩ z w hzw
    by_cases hzx : z = x
    · subst z
      simp only [store_lookup_same] at hzw
      cases hzw
      exact hxy
    · rw [store_lookup_of_ne s hzx] at hzw
      exact hs z w hzw

noncomputable def permutationCompletionFiber (s : OracleState X) (x y : X) :
    Finset (Equiv.Perm X) :=
  (permutationCompletions s).filter fun p => p x = y

theorem mem_permutationCompletionFiber_iff (s : OracleState X) (x y : X)
    (p : Equiv.Perm X) :
    p ∈ permutationCompletionFiber s x y ↔
      p ∈ permutationCompletions s ∧ p x = y := by
  simp [permutationCompletionFiber]

theorem permutationCompletions_store_eq_fiber (s : OracleState X) (x y : X)
    (hx : s.table x = none) :
    permutationCompletions (store s x y) = permutationCompletionFiber s x y := by
  ext p
  simp [mem_permutationCompletions_iff, mem_permutationCompletionFiber_iff,
    permutationCompatible_store_iff s x y hx p]

def swapOutputs (y₁ y₂ : X) (p : Equiv.Perm X) : Equiv.Perm X :=
  p.trans (Equiv.swap y₁ y₂)

theorem permutationCompatible_swapOutputs (s : OracleState X)
    (hs : CoversTable s) {y₁ y₂ : X}
    (hy₁ : y₁ ∈ availableOutputs s) (hy₂ : y₂ ∈ availableOutputs s)
    {p : Equiv.Perm X} (hp : PermutationCompatible s p) :
    PermutationCompatible s (swapOutputs y₁ y₂ p) := by
  intro z w hzw
  have hw := hs hzw
  have h₁ : w ≠ y₁ := by
    intro h; subst w; exact (mem_availableOutputs_iff s y₁).mp hy₁ hw
  have h₂ : w ≠ y₂ := by
    intro h; subst w; exact (mem_availableOutputs_iff s y₂).mp hy₂ hw
  rw [show swapOutputs y₁ y₂ p z = Equiv.swap y₁ y₂ (p z) from rfl,
    hp z w hzw]
  simp [Equiv.swap_apply_of_ne_of_ne h₁ h₂]

noncomputable def permutationCompletionFiberEquiv (s : OracleState X)
    (hs : CoversTable s) (x y₁ y₂ : X)
    (hy₁ : y₁ ∈ availableOutputs s) (hy₂ : y₂ ∈ availableOutputs s) :
    {p // p ∈ permutationCompletionFiber s x y₁} ≃
      {p // p ∈ permutationCompletionFiber s x y₂} where
  toFun p := ⟨swapOutputs y₁ y₂ p.1, by
    rw [mem_permutationCompletionFiber_iff]
    have hp := (mem_permutationCompletionFiber_iff s x y₁ p.1).mp p.2
    refine ⟨(mem_permutationCompletions_iff s _).mpr
      (permutationCompatible_swapOutputs s hs hy₁ hy₂
        ((mem_permutationCompletions_iff s _).mp hp.1)), ?_⟩
    simp [swapOutputs, hp.2]⟩
  invFun p := ⟨swapOutputs y₁ y₂ p.1, by
    rw [mem_permutationCompletionFiber_iff]
    have hp := (mem_permutationCompletionFiber_iff s x y₂ p.1).mp p.2
    refine ⟨(mem_permutationCompletions_iff s _).mpr
      (permutationCompatible_swapOutputs s hs hy₁ hy₂
        ((mem_permutationCompletions_iff s _).mp hp.1)), ?_⟩
    simp [swapOutputs, hp.2]⟩
  left_inv p := by
    apply Subtype.ext
    ext z
    simp [swapOutputs]
  right_inv p := by
    apply Subtype.ext
    ext z
    simp [swapOutputs]

theorem card_permutationCompletionFiber_eq (s : OracleState X)
    (hs : CoversTable s) (x y₁ y₂ : X)
    (hy₁ : y₁ ∈ availableOutputs s) (hy₂ : y₂ ∈ availableOutputs s) :
    (permutationCompletionFiber s x y₁).card =
      (permutationCompletionFiber s x y₂).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr
    (permutationCompletionFiberEquiv s hs x y₁ y₂ hy₁ hy₂)

theorem compatible_fresh_image_available (s : OracleState X)
    (hexact : ExactUsed s) (hinj : InjectiveTable s)
    {p : Equiv.Perm X} (hp : PermutationCompatible s p)
    {x : X} (hx : s.table x = none) : p x ∈ availableOutputs s := by
  rw [mem_availableOutputs_iff]
  intro hu
  obtain ⟨z, hz⟩ := (hexact (p x)).mp hu
  have : z = x := p.injective (hp z (p x) hz)
  subst z
  rw [hx] at hz
  contradiction

theorem permutationCompletions_store_nonempty (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (x y : X) (hx : s.table x = none) (hy : y ∈ availableOutputs s) :
    (permutationCompletions (store s x y)).Nonempty := by
  obtain ⟨p, hp⟩ := hcomp
  have hpc := (mem_permutationCompletions_iff s p).mp hp
  have hpx := compatible_fresh_image_available s hexact hinj hpc hx
  rw [permutationCompletions_store_eq_fiber s x y hx]
  exact ⟨swapOutputs (p x) y p, by
    rw [mem_permutationCompletionFiber_iff]
    exact ⟨(mem_permutationCompletions_iff s _).mpr
      (permutationCompatible_swapOutputs s hs hpx hy hpc), by
        simp [swapOutputs]⟩⟩

theorem card_permutationCompletions_eq_mul_fiber (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (x y : X) (hx : s.table x = none) (hy : y ∈ availableOutputs s) :
    (permutationCompletions s).card =
      (availableOutputs s).card * (permutationCompletionFiber s x y).card := by
  classical
  calc
    (permutationCompletions s).card = ∑ z ∈ availableOutputs s,
        ((permutationCompletions s).filter fun p => p x = z).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact compatible_fresh_image_available s hexact hinj
        ((mem_permutationCompletions_iff s p).mp hp) hx
    _ = ∑ z ∈ availableOutputs s,
        (permutationCompletionFiber s x z).card := by rfl
    _ = ∑ _z ∈ availableOutputs s,
        (permutationCompletionFiber s x y).card := by
      apply Finset.sum_congr rfl
      intro z hz
      exact card_permutationCompletionFiber_eq s hs x z y hz hy
    _ = _ := by simp

noncomputable def uniformPermutationCompletion (s : OracleState X)
    (h : (permutationCompletions s).Nonempty) : PMF (Equiv.Perm X) :=
  PMF.uniformOfFinset (permutationCompletions s) h

noncomputable def permutationCompletionAfter (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (x : X) (hx : s.table x = none) (y : X) : PMF (Equiv.Perm X) :=
  if hy : y ∈ availableOutputs s then
    uniformPermutationCompletion (store s x y)
      (permutationCompletions_store_nonempty s hs hexact hinj hcomp x y hx hy)
  else PMF.pure 1

theorem uniformPermutationCompletion_fresh (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (x : X) (hx : s.table x = none)
    (havail : (availableOutputs s).Nonempty) :
    (PMF.uniformOfFinset (availableOutputs s) havail).bind
        (permutationCompletionAfter s hs hexact hinj hcomp x hx) =
      uniformPermutationCompletion s hcomp := by
  classical
  apply PMF.ext
  intro p
  rw [PMF.bind_apply, tsum_fintype]
  simp only [permutationCompletionAfter, uniformPermutationCompletion,
    PMF.uniformOfFinset_apply]
  by_cases hp : p ∈ permutationCompletions s
  · have hpc := (mem_permutationCompletions_iff s p).mp hp
    have hpx := compatible_fresh_image_available s hexact hinj hpc hx
    have hmem : ∀ y, p ∈ permutationCompletions (store s x y) ↔ p x = y := by
      intro y
      rw [permutationCompletions_store_eq_fiber s x y hx,
        mem_permutationCompletionFiber_iff]
      simp [hp]
    rw [Fintype.sum_eq_single (p x)]
    · simp only [hpx, ↓reduceIte, dif_pos, PMF.uniformOfFinset_apply,
        (hmem (p x)).mpr rfl, hp, if_true]
      rw [permutationCompletions_store_eq_fiber s x (p x) hx,
        card_permutationCompletions_eq_mul_fiber s hs hexact hinj x (p x) hx hpx]
      push_cast
      rw [ENNReal.mul_inv (by left; simpa using Finset.card_ne_zero.mpr havail)
        (by left; simp)]
    · intro y hne
      by_cases hy : y ∈ availableOutputs s
      · simp [hy, hmem y, hne, Ne.symm hne]
      · simp [hy]
  · have hn : ∀ y, p ∉ permutationCompletions (store s x y) := by
      intro y hpy
      apply hp
      rw [mem_permutationCompletions_iff]
      exact ((permutationCompatible_store_iff s x y hx p).mp
        ((mem_permutationCompletions_iff _ _).mp hpy)).1
    simp [hp]
    intro y hy
    simp [hy, uniformPermutationCompletion, PMF.uniformOfFinset_apply, hn y]

theorem pmf_bind_congr_support (p : PMF Α) (f g : Α → PMF Β)
    (h : ∀ a, p a ≠ 0 → f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

theorem completionInteraction_eq_lazyRP (Q : QueryFunction X X) (fuel : ℕ)
    (tr : Transcript X X) (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (hcap : s.usedOutputs.card + fuel ≤ Fintype.card X) :
    (uniformPermutationCompletion s hcomp).map
        (fun p => interact Q (statelessSystem fun x => p x) fuel tr) =
      (runLazy Q rpStep fuel tr s).map Prod.fst := by
  induction fuel generalizing tr s with
  | zero =>
      rw [show (fun p : Equiv.Perm X =>
          interact Q (statelessSystem fun x => p x) 0 tr) =
        Function.const (Equiv.Perm X) tr by funext p; rfl, PMF.map_const]
      simp [runLazy, PMF.pure_map]
  | succ fuel ih =>
      cases hQ : Q.next (responses tr) with
      | none =>
          rw [show (fun p : Equiv.Perm X =>
              interact Q (statelessSystem fun x => p x) (fuel + 1) tr) =
            Function.const (Equiv.Perm X) tr by
              funext p; simp [interact, hQ], PMF.map_const]
          simp [runLazy, hQ, PMF.pure_map]
      | some x =>
          cases hx : s.table x with
          | some y =>
              have hpoint : ∀ p, uniformPermutationCompletion s hcomp p ≠ 0 →
                  interact Q (statelessSystem fun z => p z) (fuel + 1) tr =
                    interact Q (statelessSystem fun z => p z) fuel
                      (tr ++ [(x, y)]) := by
                intro p hp
                have hpmem : p ∈ permutationCompletions s := by
                  by_contra hn
                  exact hp (by simp [uniformPermutationCompletion,
                    PMF.uniformOfFinset_apply, hn])
                have hpx : p x = y :=
                  ((mem_permutationCompletions_iff s p).mp hpmem) x y hx
                simp only [interact, hQ, statelessSystem]
                have hlast : NonemptyHistory.last
                    (NonemptyHistory.ofList (queries tr ++ [x]) (by simp)) = x := by
                  unfold NonemptyHistory.last
                  simp only [NonemptyHistory.toList_ofList]
                  simp
                simp [hlast, hpx]
              rw [pmf_map_congr_support _ _ _ hpoint]
              rw [ih (tr := tr ++ [(x, y)]) (s := s) hs hexact hinj hcomp (by omega)]
              simp [runLazy, hQ, rpStep, hx, PMF.pure_bind]
          | none =>
              have hlt : s.usedOutputs.card < Fintype.card X := by omega
              have havail := availableOutputs_nonempty_of_card_lt s hlt
              rw [← uniformPermutationCompletion_fresh s hs hexact hinj hcomp x hx havail,
                PMF.map_bind]
              let sample := PMF.uniformOfFinset (availableOutputs s) havail
              let next : X → PMF (Transcript X X) := fun y =>
                (runLazy Q rpStep fuel (tr ++ [(x, y)]) (store s x y)).map Prod.fst
              have hnext : ∀ y, sample y ≠ 0 →
                  (permutationCompletionAfter s hs hexact hinj hcomp x hx y).map
                      (fun p => interact Q (statelessSystem fun z => p z)
                        (fuel + 1) tr) = next y := by
                intro y hyprob
                have hy : y ∈ availableOutputs s := by
                  by_contra hn
                  exact hyprob (by simp [sample, PMF.uniformOfFinset_apply, hn])
                have hyn : y ∉ s.usedOutputs := (mem_availableOutputs_iff s y).mp hy
                have hstore := permutationCompletions_store_nonempty s hs hexact hinj
                  hcomp x y hx hy
                simp only [permutationCompletionAfter, dif_pos hy]
                have hbranch :
                    (uniformPermutationCompletion (store s x y) hstore).map
                        (fun p => interact Q (statelessSystem fun z => p z)
                          (fuel + 1) tr) =
                      (uniformPermutationCompletion (store s x y) hstore).map
                        (fun p => interact Q (statelessSystem fun z => p z) fuel
                          (tr ++ [(x, y)])) := by
                  apply pmf_map_congr_support
                  intro p hp
                  have hpmem : p ∈ permutationCompletions (store s x y) := by
                    by_contra hn
                    exact hp (by simp [uniformPermutationCompletion,
                      PMF.uniformOfFinset_apply, hn])
                  have hpy : p x = y :=
                    ((permutationCompatible_store_iff s x y hx p).mp
                      ((mem_permutationCompletions_iff _ _).mp hpmem)).2
                  simp only [interact, hQ, statelessSystem]
                  have hlast : NonemptyHistory.last
                      (NonemptyHistory.ofList (queries tr ++ [x]) (by simp)) = x := by
                    unfold NonemptyHistory.last
                    simp only [NonemptyHistory.toList_ofList]
                    simp
                  simp [hlast, hpy]
                rw [hbranch]
                have hcap' : (store s x y).usedOutputs.card + fuel ≤
                    Fintype.card X := by
                  simp only [store_used, Finset.card_insert_of_notMem hyn]
                  omega
                exact ih (tr := tr ++ [(x, y)]) (s := store s x y)
                  (store_covers s x y hs) (store_exact s x y hx hexact)
                  (store_injective s x y hinj hx hyn hs) hstore hcap'
              rw [pmf_bind_congr_support sample _ next hnext]
              simp [sample, next, runLazy, hQ, rpStep, hx, havail,
                PMF.map_bind, PMF.map_comp]

theorem uniformPermutationCompletion_initial_map :
    (uniformPermutationCompletion (initialState X) (by simp)).map
        (fun p : Equiv.Perm X => (p : X → X)) =
      (PMF.uniformOfFintype (Equiv.Perm X)).map
        (fun p : Equiv.Perm X => (p : X → X)) := by
  apply congrArg (fun p : PMF (Equiv.Perm X) =>
    p.map (fun e : Equiv.Perm X => (e : X → X)))
  apply PMF.ext
  intro p
  simp [uniformPermutationCompletion, permutationCompletions_initial,
    PMF.uniformOfFintype_apply]

theorem transcriptDistribution_randomPermutation_eq_lazy
    (q : ℕ) (Q : QueryFunction X X) (hq : q ≤ Fintype.card X) :
    transcriptDistribution q Q (randomPermutationSystem (X := X)) =
      visible (lazyRP Q q) := by
  rw [transcriptDistribution, randomPermutationSystem, randomStatelessSystem,
    PMF.map_comp]
  change ((PMF.uniformOfFintype (Equiv.Perm X)).map
      (fun p : Equiv.Perm X => (p : X → X))).map
        (fun f => interact Q (statelessSystem f) q []) = _
  rw [← uniformPermutationCompletion_initial_map, PMF.map_comp]
  exact completionInteraction_eq_lazyRP Q q [] (initialState X)
    initial_covers initial_exact initial_injective (by simp) (by simpa using hq)

/-! ## Native switching coupling -/

noncomputable def freshOutputCoupling (s : OracleState X)
    (havail : (availableOutputs s).Nonempty) : PMF (X × X) :=
  (PMF.uniformOfFintype X).bind fun y =>
    if y ∈ availableOutputs s then PMF.pure (y, y)
    else (PMF.uniformOfFinset (availableOutputs s) havail).map fun z => (y, z)

theorem freshOutputCoupling_fst (s : OracleState X)
    (havail : (availableOutputs s).Nonempty) :
    (freshOutputCoupling s havail).map Prod.fst = PMF.uniformOfFintype X := by
  classical
  rw [freshOutputCoupling, PMF.map_bind]
  have h : ∀ y : X,
      (if y ∈ availableOutputs s then PMF.pure (y, y)
       else (PMF.uniformOfFinset (availableOutputs s) havail).map
         fun z => (y, z)).map Prod.fst = PMF.pure y := by
    intro y
    by_cases hy : y ∈ availableOutputs s
    · simp [hy, PMF.pure_map]
    · simp only [hy, ↓reduceIte, PMF.map_comp]
      rw [show (Prod.fst ∘ fun z : X => (y, z)) = Function.const X y by
        funext z; rfl, PMF.map_const]
  simp_rw [h]
  exact PMF.bind_pure (p := PMF.uniformOfFintype X)

private theorem ennreal_mixture (N A U : ℕ) (hA : 0 < A) (h : A + U = N) :
    ((N : ENNReal)⁻¹) * (1 + (U : ENNReal) * (A : ENNReal)⁻¹) =
      (A : ENNReal)⁻¹ := by
  have hN : N ≠ 0 := by omega
  have hAn : A ≠ 0 := Nat.ne_of_gt hA
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (by simp [hN])
      (ENNReal.add_ne_top.mpr ⟨by simp,
        ENNReal.mul_ne_top (by simp) (by simp [hAn])⟩))
    (by simp [hAn])).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_add (by simp)
    (by apply ENNReal.mul_ne_top <;> simp [hAn])]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_one]
  have hAr : (A : ℝ) ≠ 0 := by exact_mod_cast hAn
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp
  exact_mod_cast h

private theorem sum_mixture (S : Finset X) {a : X} (ha : a ∈ S) (c : ENNReal) :
    (∑ b : X, if b ∈ S then (if a = b then 1 else 0) else c) =
      1 + ((Fintype.card X - S.card : ℕ) : ENNReal) * c := by
  rw [Finset.sum_ite]
  simp [ha]
  congr 2
  norm_cast
  rw [show ({x : X | x ∉ S} : Finset X) = Finset.univ \ S by ext x; simp,
    Finset.card_sdiff]
  simp

theorem freshOutputCoupling_snd (s : OracleState X)
    (havail : (availableOutputs s).Nonempty) :
    (freshOutputCoupling s havail).map Prod.snd =
      PMF.uniformOfFinset (availableOutputs s) havail := by
  classical
  rw [freshOutputCoupling, PMF.map_bind]
  have hinner : ∀ y : X,
      (if y ∈ availableOutputs s then PMF.pure (y, y)
       else (PMF.uniformOfFinset (availableOutputs s) havail).map
         fun z => (y, z)).map Prod.snd =
      if y ∈ availableOutputs s then PMF.pure y
      else PMF.uniformOfFinset (availableOutputs s) havail := by
    intro y
    by_cases hy : y ∈ availableOutputs s
    · simp [hy, PMF.pure_map]
    · simp only [hy, ↓reduceIte, PMF.map_comp]
      rw [show (Prod.snd ∘ fun z : X => (y, z)) = id by funext z; rfl,
        PMF.map_id]
  simp_rw [hinner]
  apply PMF.ext
  intro a
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFinset_apply]
  rw [tsum_fintype]
  by_cases ha : a ∈ availableOutputs s
  · simp only [ha, ↓reduceIte]
    have ht : ∀ b : X,
        (if b ∈ availableOutputs s then PMF.pure b
         else PMF.uniformOfFinset (availableOutputs s) havail) a =
        if b ∈ availableOutputs s then (if a = b then 1 else 0)
        else ((availableOutputs s).card : ENNReal)⁻¹ := by
      intro b
      by_cases hb : b ∈ availableOutputs s <;>
        simp [hb, ha, PMF.pure_apply, PMF.uniformOfFinset_apply]
    simp_rw [ht]
    rw [← Finset.mul_sum, sum_mixture (availableOutputs s) ha]
    apply ennreal_mixture
    · exact Finset.card_pos.mpr havail
    · exact Nat.add_sub_of_le (Finset.card_le_univ (availableOutputs s))
  · simp only [ha, ↓reduceIte]
    have hz : ∀ i : X,
        (if i ∈ availableOutputs s then PMF.pure i
         else PMF.uniformOfFinset (availableOutputs s) havail) a = 0 := by
      intro i
      by_cases hi : i ∈ availableOutputs s
      · have hai : a ≠ i := fun h => ha (h ▸ hi)
        simp [hi, hai]
      · simp [hi, ha, PMF.uniformOfFinset_apply]
    simp_rw [hz]
    simp

noncomputable def freshOutputFailure (s : OracleState X)
    (havail : (availableOutputs s).Nonempty) : ℝ :=
  (((freshOutputCoupling s havail).map fun yz => yz.1 != yz.2) true).toReal

theorem freshOutputFailure_eq (s : OracleState X)
    (havail : (availableOutputs s).Nonempty) :
    freshOutputFailure s havail =
      (s.usedOutputs.card : ℝ) / Fintype.card X := by
  classical
  rw [freshOutputFailure, freshOutputCoupling, PMF.map_bind]
  have hinner : ∀ y : X,
      (if y ∈ availableOutputs s then PMF.pure (y, y)
       else (PMF.uniformOfFinset (availableOutputs s) havail).map
         fun z => (y, z)).map (fun yz => yz.1 != yz.2) =
      PMF.pure (decide (y ∉ availableOutputs s)) := by
    intro y
    by_cases hy : y ∈ availableOutputs s
    · simp [hy, PMF.pure_map]
    · simp only [hy, ↓reduceIte, PMF.map_comp]
      apply PMF.ext
      intro b
      cases b with
      | false =>
          simp [PMF.map_apply, PMF.uniformOfFinset_apply, tsum_fintype, hy]
      | true =>
          rw [PMF.map_apply, tsum_fintype]
          have ht : ∀ z : X,
              (@ite ENNReal
                (true = ((fun yz : X × X => yz.1 != yz.2) ∘ fun z => (y, z)) z)
                (Classical.propDecidable _)
                ((PMF.uniformOfFinset (availableOutputs s) havail) z) 0) =
              if z ∈ availableOutputs s then
                ((availableOutputs s).card : ENNReal)⁻¹ else 0 := by
            intro z
            by_cases hz : z ∈ availableOutputs s
            · have hyz : y ≠ z := fun h => hy (h ▸ hz)
              simp [hz, hyz, PMF.uniformOfFinset_apply]
            · simp [hz, PMF.uniformOfFinset_apply]
          rw [show (PMF.pure (decide (¬False)) : PMF Bool) true = 1 by simp]
          calc
            _ = ∑ z : X, if z ∈ availableOutputs s then
                ((availableOutputs s).card : ENNReal)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro z hz
              exact ht z
            _ = 1 := by
              rw [Finset.sum_ite]
              simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
                nsmul_eq_mul]
              have hf : Finset.univ.filter (fun x => x ∈ availableOutputs s) =
                  availableOutputs s := by ext x; simp
              rw [hf]
              apply ENNReal.mul_inv_cancel
              · exact_mod_cast Finset.card_ne_zero.mpr havail
              · simp
  simp_rw [hinner]
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]
  rw [tsum_fintype]
  simp [availableOutputs, Finset.sum_ite, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv]

noncomputable def pmfProduct (p : PMF Α) (q : PMF Β) : PMF (Α × Β) :=
  p.bind fun a => q.map fun b => (a, b)

theorem pmfProduct_map_fst (p : PMF Α) (q : PMF Β) :
    (pmfProduct p q).map Prod.fst = p := by
  rw [pmfProduct, PMF.map_bind]
  have h : ∀ a : Α, (q.map fun b => (a, b)).map Prod.fst = PMF.pure a := by
    intro a
    rw [PMF.map_comp]
    rw [show (Prod.fst ∘ fun b : Β => (a, b)) = Function.const Β a by
      funext b; rfl, PMF.map_const]
  simp_rw [h]
  exact PMF.bind_pure (p := p)

theorem pmfProduct_map_snd (p : PMF Α) (q : PMF Β) :
    (pmfProduct p q).map Prod.snd = q := by
  rw [pmfProduct, PMF.map_bind]
  have h : ∀ a : Α, (q.map fun b => (a, b)).map Prod.snd = q := by
    intro a
    rw [PMF.map_comp]
    exact PMF.map_id q
  simp_rw [h]
  exact PMF.bind_const (p := p) (q := q)

/-- Global coupling of the two native Section 3.1 lazy executions.  Once the
outputs disagree, the two exact continuations are sampled independently. -/
noncomputable def runCoupled (Q : QueryFunction X X) :
    ℕ → Transcript X X → OracleState X →
      PMF ((Transcript X X × OracleState X) ×
        (Transcript X X × OracleState X))
  | 0, tr, s => PMF.pure ((tr, s), (tr, s))
  | fuel + 1, tr, s =>
      match Q.next (responses tr) with
      | none => PMF.pure ((tr, s), (tr, s))
      | some x =>
          match s.table x with
          | some y => runCoupled Q fuel (tr ++ [(x, y)]) s
          | none =>
              if havail : (availableOutputs s).Nonempty then
                (freshOutputCoupling s havail).bind fun yz =>
                  if yz.1 = yz.2 then
                    runCoupled Q fuel (tr ++ [(x, yz.1)]) (store s x yz.1)
                  else
                    pmfProduct
                      (runLazy Q rfStep fuel (tr ++ [(x, yz.1)])
                        (store s x yz.1))
                      (runLazy Q rpStep fuel (tr ++ [(x, yz.2)])
                        (store s x yz.2))
              else pmfProduct (runLazy Q rfStep (fuel + 1) tr s)
                (runLazy Q rpStep (fuel + 1) tr s)

theorem runCoupled_map_fst (Q : QueryFunction X X) (fuel : ℕ)
    (tr : Transcript X X) (s : OracleState X) :
    (runCoupled Q fuel tr s).map Prod.fst = runLazy Q rfStep fuel tr s := by
  induction fuel generalizing tr s with
  | zero => simp [runCoupled, runLazy, PMF.pure_map]
  | succ fuel ih =>
      rw [runCoupled, runLazy]
      cases hQ : Q.next (responses tr) with
      | none => simp [runLazy, hQ, PMF.pure_map]
      | some x =>
          simp only [hQ]
          cases hx : s.table x with
          | some y => simp [hx, rfStep, PMF.pure_bind, ih]
          | none =>
              simp only [hx, rfStep]
              split
              · rename_i havail
                rw [PMF.map_bind]
                have hinner : ∀ yz : X × X,
                    ((if yz.1 = yz.2 then
                        runCoupled Q fuel (tr ++ [(x, yz.1)]) (store s x yz.1)
                      else pmfProduct
                        (runLazy Q rfStep fuel (tr ++ [(x, yz.1)])
                          (store s x yz.1))
                        (runLazy Q rpStep fuel (tr ++ [(x, yz.2)])
                          (store s x yz.2))).map Prod.fst) =
                      runLazy Q rfStep fuel (tr ++ [(x, yz.1)])
                        (store s x yz.1) := by
                  rintro ⟨a,b⟩
                  by_cases h : a = b
                  · subst b; simp [ih]
                  · simp [h, pmfProduct_map_fst]
                simp_rw [hinner]
                rw [PMF.bind_map]
                rw [← freshOutputCoupling_fst s havail, PMF.bind_map]
                rfl
              · exact pmfProduct_map_fst _ _

theorem runCoupled_map_snd (Q : QueryFunction X X) (fuel : ℕ)
    (tr : Transcript X X) (s : OracleState X) :
    (runCoupled Q fuel tr s).map Prod.snd = runLazy Q rpStep fuel tr s := by
  induction fuel generalizing tr s with
  | zero => simp [runCoupled, runLazy, PMF.pure_map]
  | succ fuel ih =>
      rw [runCoupled, runLazy]
      cases hQ : Q.next (responses tr) with
      | none => simp [runLazy, hQ, PMF.pure_map]
      | some x =>
          simp only [hQ]
          cases hx : s.table x with
          | some y =>
              rw [ih]
              symm
              simp [runLazy, hQ, rpStep, hx]
          | none =>
              simp only [hx, rpStep]
              split
              · rename_i havail
                rw [PMF.map_bind]
                have hinner : ∀ yz : X × X,
                    ((if yz.1 = yz.2 then
                        runCoupled Q fuel (tr ++ [(x, yz.1)]) (store s x yz.1)
                      else pmfProduct
                        (runLazy Q rfStep fuel (tr ++ [(x, yz.1)])
                          (store s x yz.1))
                        (runLazy Q rpStep fuel (tr ++ [(x, yz.2)])
                          (store s x yz.2))).map Prod.snd) =
                      runLazy Q rpStep fuel (tr ++ [(x, yz.2)])
                        (store s x yz.2) := by
                  rintro ⟨a,b⟩
                  by_cases h : a = b
                  · subst b; simp [ih]
                  · simp [h, pmfProduct_map_snd]
                simp_rw [hinner]
                rw [show runLazy Q rpStep (fuel + 1) tr s =
                    ((PMF.uniformOfFinset (availableOutputs s) havail).map
                      fun y => (y, store s x y)).bind fun ys =>
                        runLazy Q rpStep fuel (tr ++ [(x, ys.1)]) ys.2 by
                    simp [runLazy, hQ, rpStep, hx, havail]]
                rw [PMF.bind_map]
                rw [← freshOutputCoupling_snd s havail, PMF.bind_map]
                rfl
              · exact pmfProduct_map_snd _ _

noncomputable def eventMass (p : PMF Α) (event : Α → Bool) : ENNReal :=
  (p.map event) true

theorem eventMass_le_one (p : PMF Α) (event : Α → Bool) :
    eventMass p event ≤ 1 := PMF.coe_le_one _ _

theorem freshOutputFailure_mass_eq (s : OracleState X)
    (havail : (availableOutputs s).Nonempty) :
    eventMass (freshOutputCoupling s havail) (fun yz => yz.1 != yz.2) =
      (s.usedOutputs.card : ENNReal) * (Fintype.card X : ENNReal)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (by simp) (by simp))).mp
  simpa [eventMass, freshOutputFailure, div_eq_mul_inv,
    ENNReal.toReal_mul, ENNReal.toReal_inv] using freshOutputFailure_eq s havail

theorem eventMass_bind_le (p : PMF Α) (k : Α → PMF Β)
    (event : Β → Bool) (bad : Α → Bool) (c : ENNReal)
    (h : ∀ a, eventMass (k a) event ≤ (if bad a then 1 else 0) + c) :
    eventMass (p.bind k) event ≤ eventMass p bad + c := by
  rw [eventMass, PMF.map_bind, PMF.bind_apply]
  calc
    (∑' a, p a * ((k a).map event) true) ≤
        ∑' a, p a * ((if bad a then 1 else 0) + c) := by
      apply ENNReal.tsum_le_tsum
      intro a
      gcongr
      exact h a
    _ = (∑' a, p a * (if bad a then 1 else 0)) + ∑' a, p a * c := by
      simp_rw [mul_add]
      exact ENNReal.tsum_add
    _ = eventMass p bad + c := by
      rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
      congr 1
      rw [eventMass, PMF.map_apply]
      apply tsum_congr
      intro a
      by_cases ha : bad a = true <;> simp [ha]

noncomputable def ennCollisionBudgetFrom (N : ℕ) : ℕ → ℕ → ENNReal
  | _, 0 => 0
  | i, fuel + 1 =>
      (i : ENNReal) * (N : ENNReal)⁻¹ + ennCollisionBudgetFrom N (i + 1) fuel

theorem ennCollisionBudgetFrom_mono_fuel (N i fuel : ℕ) :
    ennCollisionBudgetFrom N i fuel ≤ ennCollisionBudgetFrom N i (fuel + 1) := by
  induction fuel generalizing i with
  | zero => simp [ennCollisionBudgetFrom]
  | succ fuel ih =>
      simp only [ennCollisionBudgetFrom]
      gcongr
      exact ih (i + 1)

def resultMismatch
    (out : (Transcript X X × OracleState X) ×
      (Transcript X X × OracleState X)) : Bool :=
  out.1.1 != out.2.1

theorem runCoupled_failureMass_le (Q : QueryFunction X X)
    (fuel i : ℕ) (tr : Transcript X X) (s : OracleState X)
    (hcard : s.usedOutputs.card ≤ i)
    (hcap : i + fuel ≤ Fintype.card X) :
    eventMass (runCoupled Q fuel tr s) resultMismatch ≤
      ennCollisionBudgetFrom (Fintype.card X) i fuel := by
  induction fuel generalizing i tr s with
  | zero => simp [runCoupled, eventMass, resultMismatch, ennCollisionBudgetFrom,
      PMF.pure_map]
  | succ fuel ih =>
      rw [runCoupled]
      cases hQ : Q.next (responses tr) with
      | none => simp [hQ, eventMass, resultMismatch, ennCollisionBudgetFrom,
          PMF.pure_map]
      | some x =>
          simp only [hQ]
          cases hx : s.table x with
          | some y =>
              exact le_trans (ih i (tr ++ [(x,y)]) s hcard (by omega))
                (ennCollisionBudgetFrom_mono_fuel (Fintype.card X) i fuel)
          | none =>
              have hlt : s.usedOutputs.card < Fintype.card X :=
                lt_of_le_of_lt hcard (by omega)
              have havail := availableOutputs_nonempty_of_card_lt s hlt
              simp only [hx, havail, dite_true]
              let c := ennCollisionBudgetFrom (Fintype.card X) (i + 1) fuel
              have hk : ∀ yz : X × X,
                  eventMass
                    (if yz.1 = yz.2 then
                      runCoupled Q fuel (tr ++ [(x, yz.1)]) (store s x yz.1)
                    else pmfProduct
                      (runLazy Q rfStep fuel (tr ++ [(x, yz.1)]) (store s x yz.1))
                      (runLazy Q rpStep fuel (tr ++ [(x, yz.2)]) (store s x yz.2)))
                    resultMismatch ≤ (if yz.1 != yz.2 then 1 else 0) + c := by
                rintro ⟨a,b⟩
                by_cases hab : a = b
                · subst b
                  have hs : (store s x a).usedOutputs.card ≤ i + 1 := by
                    simp only [store_used]
                    exact le_trans (Finset.card_insert_le a s.usedOutputs)
                      (Nat.add_le_add_right hcard 1)
                  have hi := ih (i + 1) (tr ++ [(x,a)]) (store s x a) hs (by omega)
                  simpa [c] using hi
                · simp only [hab, dite_false]
                  have hm : eventMass (pmfProduct
                      (runLazy Q rfStep fuel (tr ++ [(x,a)]) (store s x a))
                      (runLazy Q rpStep fuel (tr ++ [(x,b)]) (store s x b)))
                      resultMismatch ≤ 1 := eventMass_le_one _ _
                  simpa [hab] using le_trans hm (le_add_right (le_refl 1))
              refine le_trans (eventMass_bind_le (freshOutputCoupling s havail) _
                resultMismatch (fun yz => yz.1 != yz.2) c hk) ?_
              rw [freshOutputFailure_mass_eq]
              simp only [ennCollisionBudgetFrom, c]
              gcongr

/-! ## Closing the native coupling bound inside Section 3.1 -/

theorem ennCollisionBudgetFrom_ne_top (N i fuel : ℕ) (hN : N ≠ 0) :
    ennCollisionBudgetFrom N i fuel ≠ ⊤ := by
  induction fuel generalizing i with
  | zero => simp [ennCollisionBudgetFrom]
  | succ fuel ih =>
      rw [ennCollisionBudgetFrom]
      exact ENNReal.add_ne_top.mpr ⟨
        ENNReal.mul_ne_top (by simp) (by simp [hN]), ih (i + 1)⟩

noncomputable def realCollisionBudgetFrom (N : ℕ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | i, fuel + 1 =>
      (i : ℝ) / (N : ℝ) + realCollisionBudgetFrom N (i + 1) fuel

theorem ennCollisionBudgetFrom_toReal (N i fuel : ℕ) (hN : N ≠ 0) :
    (ennCollisionBudgetFrom N i fuel).toReal =
      realCollisionBudgetFrom N i fuel := by
  induction fuel generalizing i with
  | zero => simp [ennCollisionBudgetFrom, realCollisionBudgetFrom]
  | succ fuel ih =>
      rw [ennCollisionBudgetFrom, realCollisionBudgetFrom,
        ENNReal.toReal_add
          (ENNReal.mul_ne_top (by simp) (by simp [hN]))
          (ennCollisionBudgetFrom_ne_top N (i + 1) fuel hN),
        ENNReal.toReal_mul, ENNReal.toReal_inv (N : ENNReal), ih]
      simp [div_eq_mul_inv]

theorem realCollisionBudgetFrom_eq (N i fuel : ℕ) (hN : N ≠ 0) :
    realCollisionBudgetFrom N i fuel =
      (fuel : ℝ) * (2 * (i : ℝ) + (fuel : ℝ) - 1) /
        (2 * (N : ℝ)) := by
  induction fuel generalizing i with
  | zero => simp [realCollisionBudgetFrom]
  | succ fuel ih =>
      rw [realCollisionBudgetFrom, ih]
      push_cast
      field_simp
      ring

universe v

/-- A proof coupling, used only to compare the two Section 3.1 transcript laws. -/
structure Coupling {Ω : Type v} (left right : PMF Ω) where
  joint : PMF (Ω × Ω)
  map_fst : joint.map Prod.fst = left
  map_snd : joint.map Prod.snd = right

noncomputable def Coupling.fullFailure {Ω : Type v} [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right) : ℝ :=
  ((c.joint.map fun z => z.1 != z.2) true).toReal

noncomputable def Coupling.decisionFailure {Ω : Type v}
    {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) : ℝ :=
  ((c.joint.map fun z => decision z.1 != decision z.2) true).toReal

noncomputable def eventProbability {Ω : Type v}
    (p : PMF Ω) (decision : Ω → Bool) : ℝ :=
  ((p.map decision) true).toReal

noncomputable def pmfAdvantage {Ω : Type v}
    (left right : PMF Ω) (decision : Ω → Bool) : ℝ :=
  |eventProbability left decision - eventProbability right decision|

theorem eventProbability_le_one {Ω : Type v}
    (p : PMF Ω) (decision : Ω → Bool) : eventProbability p decision ≤ 1 := by
  rw [eventProbability]
  have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
    (PMF.coe_le_one (p.map decision) true)
  simpa using h

theorem pmfAdvantage_le_coupling_failure {Ω : Type v} [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) :
    pmfAdvantage left right decision ≤ c.decisionFailure decision := by
  let j : PMF (Bool × Bool) := c.joint.map fun z => (decision z.1, decision z.2)
  have hleft : left.map decision = j.map Prod.fst := by
    rw [← c.map_fst, PMF.map_comp, PMF.map_comp]
    rfl
  have hright : right.map decision = j.map Prod.snd := by
    rw [← c.map_snd, PMF.map_comp, PMF.map_comp]
    rfl
  have hfail : c.decisionFailure decision =
      (j (true, false)).toReal + (j (false, true)).toReal := by
    rw [Coupling.decisionFailure]
    have hmap : c.joint.map (fun z => decision z.1 != decision z.2) =
        j.map (fun z => z.1 != z.2) := by
      simp only [j, PMF.map_comp]
      rfl
    rw [hmap, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fintype.sum_bool]
    norm_num
    rw [ENNReal.toReal_add (j.apply_ne_top _) (j.apply_ne_top _)]
  have hleftProb : eventProbability left decision =
      (j (true, true)).toReal + (j (true, false)).toReal := by
    rw [eventProbability, hleft, PMF.map_apply, tsum_fintype,
      Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true, add_zero]
    rw [ENNReal.toReal_add (j.apply_ne_top _) (j.apply_ne_top _)]
  have hrightProb : eventProbability right decision =
      (j (true, true)).toReal + (j (false, true)).toReal := by
    rw [eventProbability, hright, PMF.map_apply, tsum_fintype,
      Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.true_eq, ↓reduceIte,
      Bool.false_eq_true, zero_add, add_zero]
    rw [ENNReal.toReal_add (j.apply_ne_top _) (j.apply_ne_top _)]
  rw [pmfAdvantage, hleftProb, hrightProb, hfail]
  have h₁ : 0 ≤ (j (true, false)).toReal := ENNReal.toReal_nonneg
  have h₂ : 0 ≤ (j (false, true)).toReal := ENNReal.toReal_nonneg
  rw [add_sub_add_left_eq_sub]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem Coupling.decisionFailure_le_fullFailure {Ω : Type v}
    [DecidableEq Ω] {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) :
    c.decisionFailure decision ≤ c.fullFailure := by
  rw [Coupling.decisionFailure, Coupling.fullFailure, PMF.map_apply, PMF.map_apply]
  apply ENNReal.toReal_mono
  · simpa only [PMF.map_apply] using
      (PMF.apply_ne_top (c.joint.map fun z => z.1 != z.2) true)
  · apply ENNReal.tsum_le_tsum
    rintro ⟨a,b⟩
    by_cases hab : a = b
    · subst b; simp
    · by_cases hd : decision a = decision b <;> simp [hab, hd]

theorem pmfAdvantage_le_fullFailure {Ω : Type v} [DecidableEq Ω]
    {left right : PMF Ω} (c : Coupling left right)
    (decision : Ω → Bool) :
    pmfAdvantage left right decision ≤ c.fullFailure :=
  le_trans (pmfAdvantage_le_coupling_failure c decision)
    (c.decisionFailure_le_fullFailure decision)

noncomputable def lazyTranscriptCoupling (Q : QueryFunction X X) (q : ℕ) :
    Coupling (visible (lazyRF Q q)) (visible (lazyRP Q q)) where
  joint := (runCoupled Q q [] (initialState X)).map
    (fun z => (z.1.1, z.2.1))
  map_fst := by
    rw [PMF.map_comp]
    change (runCoupled Q q [] (initialState X)).map
      (Prod.fst ∘ Prod.fst) = _
    rw [← PMF.map_comp, runCoupled_map_fst]
    rfl
  map_snd := by
    rw [PMF.map_comp]
    change (runCoupled Q q [] (initialState X)).map
      (Prod.fst ∘ Prod.snd) = _
    rw [← PMF.map_comp, runCoupled_map_snd]
    rfl

theorem lazyTranscriptCoupling_failure_eq (Q : QueryFunction X X) (q : ℕ) :
    (lazyTranscriptCoupling Q q).fullFailure =
      (eventMass (runCoupled Q q [] (initialState X)) resultMismatch).toReal := by
  rw [Coupling.fullFailure]
  unfold eventMass resultMismatch lazyTranscriptCoupling
  rw [PMF.map_comp]
  congr 3
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, bne_iff_ne]

theorem lazyTranscriptCoupling_failure_le (Q : QueryFunction X X) (q : ℕ)
    (hq : q ≤ Fintype.card X) :
    (lazyTranscriptCoupling Q q).fullFailure ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  rw [lazyTranscriptCoupling_failure_eq]
  have hmass := runCoupled_failureMass_le Q q 0 [] (initialState X)
    (by simp) (by simpa using hq)
  refine le_trans (ENNReal.toReal_mono
    (ennCollisionBudgetFrom_ne_top (Fintype.card X) 0 q Fintype.card_ne_zero)
    hmass) ?_
  rw [ennCollisionBudgetFrom_toReal _ _ _ Fintype.card_ne_zero,
    realCollisionBudgetFrom_eq _ _ _ Fintype.card_ne_zero]
  ring_nf
  exact le_rfl

theorem pmfAdvantage_le_one {Ω : Type v} (left right : PMF Ω)
    (decision : Ω → Bool) : pmfAdvantage left right decision ≤ 1 := by
  rw [pmfAdvantage]
  have hl0 : 0 ≤ eventProbability left decision := ENNReal.toReal_nonneg
  have hr0 : 0 ≤ eventProbability right decision := ENNReal.toReal_nonneg
  have hl1 := eventProbability_le_one left decision
  have hr1 := eventProbability_le_one right decision
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The PRP/PRF switching lemma proved wholly from the Section 3.1 semantics. -/
theorem deterministic_prp_prf_switching
    (A : DeterministicDistinguisher q X X) :
    distinguishingAdvantage
        (randomFunctionSystem (X := X))
        (randomPermutationSystem (X := X)) A ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  by_cases hq : q ≤ Fintype.card X
  · simp only [distinguishingAdvantage, acceptanceProbability]
    rw [transcriptDistribution_randomFunction_eq_lazy,
      transcriptDistribution_randomPermutation_eq_lazy _ _ hq]
    change pmfAdvantage (visible (lazyRF A.query q))
      (visible (lazyRP A.query q)) A.decision ≤ _
    exact le_trans
      (pmfAdvantage_le_fullFailure (lazyTranscriptCoupling A.query q) A.decision)
      (lazyTranscriptCoupling_failure_le A.query q hq)
  · have hbad : distinguishingAdvantage
        (randomFunctionSystem (X := X))
        (randomPermutationSystem (X := X)) A ≤ 1 := by
      rw [distinguishingAdvantage, acceptanceProbability]
      change pmfAdvantage
        (transcriptDistribution q A.query (randomFunctionSystem (X := X)))
        (transcriptDistribution q A.query (randomPermutationSystem (X := X)))
        A.decision ≤ 1
      exact pmfAdvantage_le_one _ _ _
    have hNnat : 0 < Fintype.card X := Fintype.card_pos
    have hN1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hNnat
    have hqnat : Fintype.card X + 1 ≤ q := by omega
    have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast hNnat
    have hqreal : (Fintype.card X : ℝ) + 1 ≤ q := by exact_mod_cast hqnat
    have hone : (1 : ℝ) ≤
        (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card X)).2
      have hq2 : (2 : ℝ) ≤ q := by linarith
      have hminus : (Fintype.card X : ℝ) ≤ (q : ℝ) - 1 := by nlinarith
      have hprod := mul_le_mul hq2 hminus (le_of_lt hN)
        (by positivity : (0 : ℝ) ≤ q)
      nlinarith
    exact le_trans hbad hone

/-- Randomized Section 3.1 distinguishers follow by averaging the deterministic bound. -/
theorem randomized_prp_prf_switching (A : Distinguisher q X X) :
    randomizedAdvantage
        (randomFunctionSystem (X := X))
        (randomPermutationSystem (X := X)) A ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
  let S₀ := randomFunctionSystem (X := X)
  let S₁ := randomPermutationSystem (X := X)
  let B : ℝ := (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X)
  let w : DeterministicDistinguisher q X X → ℝ := fun a => (A a).toReal
  let u : DeterministicDistinguisher q X X → ℝ := fun a => acceptanceProbability a S₀
  let v : DeterministicDistinguisher q X X → ℝ := fun a => acceptanceProbability a S₁
  have hw : Summable w := by
    apply ENNReal.summable_toReal
    rw [A.tsum_coe]
    simp
  have hw_nonneg : ∀ a, 0 ≤ w a := fun _ => ENNReal.toReal_nonneg
  have hw_sum : ∑' a, w a = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => A.apply_ne_top a), A.tsum_coe]
    rfl
  have hu_one : ∀ a, u a ≤ 1 := by
    intro a
    exact eventProbability_le_one (transcriptDistribution q a.query S₀) a.decision
  have hv_one : ∀ a, v a ≤ 1 := by
    intro a
    exact eventProbability_le_one (transcriptDistribution q a.query S₁) a.decision
  have hwu : Summable (fun a => w a * u a) := by
    apply Summable.of_nonneg_of_le
    · intro a; exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · intro a; exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hu_one a)
    · exact hw
  have hwv : Summable (fun a => w a * v a) := by
    apply Summable.of_nonneg_of_le
    · intro a; exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · intro a; exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hv_one a)
    · exact hw
  have hdiff : Summable (fun a => w a * (u a - v a)) := by
    have h := hwu.sub hwv
    have heq : (fun a => w a * u a - w a * v a) =
        (fun a => w a * (u a - v a)) := by
      funext a
      ring
    rwa [heq] at h
  have hnorm : Summable (fun a => ‖w a * (u a - v a)‖) := hdiff.norm
  have habsSummable : Summable (fun a => w a * |u a - v a|) := by
    convert hnorm using 1
    funext a
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nonneg a)]
  have hbound : ∀ a, |u a - v a| ≤ B := by
    intro a
    simpa [u, v, S₀, S₁, B, distinguishingAdvantage] using
      deterministic_prp_prf_switching (X := X) a
  rw [randomizedAdvantage, randomizedAcceptanceProbability]
  change |(∑' a, w a * u a) - ∑' a, w a * v a| ≤ B
  rw [← hwu.tsum_sub hwv]
  have htsum : (∑' a, (w a * u a - w a * v a)) =
      ∑' a, w a * (u a - v a) := by
    apply tsum_congr
    intro a
    ring
  rw [htsum]
  calc
    |∑' a, w a * (u a - v a)| = ‖∑' a, w a * (u a - v a)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' a, ‖w a * (u a - v a)‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' a, w a * |u a - v a| := by
      apply tsum_congr
      intro a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nonneg a)]
    _ ≤ ∑' a, w a * B := by
      apply Summable.tsum_le_tsum
      · intro a
        exact mul_le_mul_of_nonneg_left (hbound a) ENNReal.toReal_nonneg
      · exact habsSummable
      · exact hw.mul_right B
    _ = B := by rw [tsum_mul_right, hw_sum, one_mul]

end InformationTheoreticSecurity.Section31.NativeSwitching
