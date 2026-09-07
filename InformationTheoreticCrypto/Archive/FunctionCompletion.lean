import InformationTheoreticCrypto.Archive.LazySampling

/-!
# Completing a lazy random-function table

This module supplies the finite counting interface used to identify whole
uniform functions with lazy sampling.
-/

namespace PRPPRFSwitching.Lazy

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]

/-- A total function agrees with every response already stored in `s`. -/
def FunctionCompatible (s : OracleState X) (f : X → X) : Prop :=
  ∀ x y, s.table x = some y → f x = y

noncomputable instance (s : OracleState X) : DecidablePred (FunctionCompatible s) :=
  fun f => Classical.propDecidable _

/-- All total functions completing the current partial table. -/
noncomputable def functionCompletions (s : OracleState X) : Finset (X → X) :=
  Finset.univ.filter (FunctionCompatible s)

theorem mem_functionCompletions_iff (s : OracleState X) (f : X → X) :
    f ∈ functionCompletions s ↔ FunctionCompatible s f := by
  simp [functionCompletions]

@[simp]
theorem functionCompletions_initial :
    functionCompletions (initialState X) = Finset.univ := by
  ext f
  simp [functionCompletions, FunctionCompatible]

theorem functionCompatible_store_iff (s : OracleState X) (x y : X)
    (hx : s.table x = none) (f : X → X) :
    FunctionCompatible (store s x y) f ↔
      FunctionCompatible s f ∧ f x = y := by
  constructor
  · intro h
    constructor
    · intro z w hzw
      have hzx : z ≠ x := by
        intro hz
        subst z
        rw [hx] at hzw
        contradiction
      exact h z w (by simpa [store_lookup_of_ne s hzx] using hzw)
    · exact h x y (store_lookup_same s x y)
  · rintro ⟨hs, hxy⟩ z w hzw
    by_cases hzx : z = x
    · subst z
      simp only [store_lookup_same] at hzw
      cases hzw
      exact hxy
    · rw [store_lookup_of_ne s hzx] at hzw
      exact hs z w hzw

theorem mem_functionCompletions_store_iff (s : OracleState X) (x y : X)
    (hx : s.table x = none) (f : X → X) :
    f ∈ functionCompletions (store s x y) ↔
      f ∈ functionCompletions s ∧ f x = y := by
  simp only [mem_functionCompletions_iff,
    functionCompatible_store_iff s x y hx f]

/-- Updating a fresh coordinate preserves compatibility with the old table. -/
theorem functionCompatible_update_fresh (s : OracleState X) (x y : X)
    (hx : s.table x = none) {f : X → X} (hf : FunctionCompatible s f) :
    FunctionCompatible s (Function.update f x y) := by
  intro z w hzw
  have hzx : z ≠ x := by
    intro hz
    subst z
    rw [hx] at hzw
    contradiction
  simp only [Function.update, hzx, ↓reduceIte]
  exact hf z w hzw

/-- Every old completion has a canonical extension in the fiber `f x = y`. -/
theorem update_mem_functionCompletions_store (s : OracleState X) (x y : X)
    (hx : s.table x = none) {f : X → X}
    (hf : f ∈ functionCompletions s) :
    Function.update f x y ∈ functionCompletions (store s x y) := by
  rw [mem_functionCompletions_store_iff s x y hx]
  exact ⟨(mem_functionCompletions_iff s _).mpr
    (functionCompatible_update_fresh s x y hx
      ((mem_functionCompletions_iff s f).mp hf)), by simp⟩

/-- Completions whose value at `x` is the prescribed output `y`. -/
noncomputable def completionFiber (s : OracleState X) (x y : X) :
    Finset (X → X) :=
  (functionCompletions s).filter fun f => f x = y

theorem mem_completionFiber_iff (s : OracleState X) (x y : X) (f : X → X) :
    f ∈ completionFiber s x y ↔
      f ∈ functionCompletions s ∧ f x = y := by
  simp [completionFiber]

theorem functionCompletions_store_eq_fiber (s : OracleState X) (x y : X)
    (hx : s.table x = none) :
    functionCompletions (store s x y) = completionFiber s x y := by
  ext f
  rw [mem_functionCompletions_store_iff s x y hx,
    mem_completionFiber_iff]

/-- All output fibers over a fresh input have the same number of completions. -/
noncomputable def completionFiberEquiv (s : OracleState X) (x y₁ y₂ : X)
    (hx : s.table x = none) :
    {f // f ∈ completionFiber s x y₁} ≃
      {f // f ∈ completionFiber s x y₂} where
  toFun f := ⟨Function.update f.1 x y₂, by
    rw [mem_completionFiber_iff]
    exact ⟨(mem_functionCompletions_iff s _).mpr
      (functionCompatible_update_fresh s x y₂ hx
        ((mem_functionCompletions_iff s f.1).mp
          ((mem_completionFiber_iff s x y₁ f.1).mp f.2).1)), by simp⟩⟩
  invFun f := ⟨Function.update f.1 x y₁, by
    rw [mem_completionFiber_iff]
    exact ⟨(mem_functionCompletions_iff s _).mpr
      (functionCompatible_update_fresh s x y₁ hx
        ((mem_functionCompletions_iff s f.1).mp
          ((mem_completionFiber_iff s x y₂ f.1).mp f.2).1)), by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    by_cases hzx : z = x
    · subst z
      simpa using ((mem_completionFiber_iff s x y₁ f.1).mp f.2).2.symm
    · simp [Function.update, hzx]
  right_inv f := by
    apply Subtype.ext
    funext z
    by_cases hzx : z = x
    · subst z
      simpa using ((mem_completionFiber_iff s x y₂ f.1).mp f.2).2.symm
    · simp [Function.update, hzx]

theorem card_completionFiber_eq (s : OracleState X) (x y₁ y₂ : X)
    (hx : s.table x = none) :
    (completionFiber s x y₁).card = (completionFiber s x y₂).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (completionFiberEquiv s x y₁ y₂ hx)

/-- The completion set is nonempty: fill undefined entries with any default. -/
theorem functionCompletions_nonempty (s : OracleState X) :
    (functionCompletions s).Nonempty := by
  let d : X := Classical.choice inferInstance
  let f : X → X := fun x => (s.table x).getD d
  refine ⟨f, (mem_functionCompletions_iff s f).mpr ?_⟩
  intro x y hxy
  simp [f, hxy]

/-- A fresh coordinate partitions completions into `|X|` equal fibers. -/
theorem card_functionCompletions_eq_mul_fiber (s : OracleState X) (x y : X)
    (hx : s.table x = none) :
    (functionCompletions s).card =
      Fintype.card X * (completionFiber s x y).card := by
  classical
  calc
    (functionCompletions s).card =
        ∑ z ∈ (Finset.univ : Finset X),
          ((functionCompletions s).filter fun f => f x = z).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro f hf
      simp
    _ = ∑ z ∈ (Finset.univ : Finset X), (completionFiber s x z).card := by
      apply Finset.sum_congr rfl
      intro z hz
      rfl
    _ = ∑ _z ∈ (Finset.univ : Finset X), (completionFiber s x y).card := by
      apply Finset.sum_congr rfl
      intro z hz
      exact card_completionFiber_eq s x z y hx
    _ = Fintype.card X * (completionFiber s x y).card := by
      simp

/-- Uniform distribution on all total completions of `s`. -/
noncomputable def uniformFunctionCompletion (s : OracleState X) : PMF (X → X) :=
  PMF.uniformOfFinset (functionCompletions s) (functionCompletions_nonempty s)

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

@[simp]
theorem uniformFunctionCompletion_initial :
    uniformFunctionCompletion (initialState X) = randomFunction X X := by
  simp [uniformFunctionCompletion, randomFunction, functionCompletions_initial,
    PMF.uniformOfFintype]

/-- Deferred-decision equation for a fresh random-function coordinate. -/
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
  · have hmem : ∀ b : X,
        (f ∈ functionCompletions (store s x b)) ↔ f x = b := by
      intro b
      rw [mem_functionCompletions_store_iff s x b hx]
      simp [hf]
    have hcard : ∀ b : X,
        (functionCompletions (store s x b)).card =
          (completionFiber s x (f x)).card := by
      intro b
      rw [functionCompletions_store_eq_fiber s x b hx]
      exact card_completionFiber_eq s x b (f x) hx
    simp_rw [hmem, hcard]
    simp only [hf, if_true]
    rw [Fintype.sum_eq_single (f x)]
    · simp only [↓reduceIte]
      rw [card_functionCompletions_eq_mul_fiber s x (f x) hx]
      push_cast
      rw [ENNReal.mul_inv (by left; simp) (by left; simp)]
    · intro b hne
      simp [hne, Ne.symm hne]
  · have hnone : ∀ b : X, f ∉ functionCompletions (store s x b) := by
      intro b hb
      exact hf ((mem_functionCompletions_store_iff s x b hx f).mp hb).1
    simp [hf, hnone]

/-- Whole-function evaluation and lazy RF sampling induce the same transcript law. -/
theorem completionTranscripts_eq_lazyRF (A : QueryStrategy X X) (fuel : ℕ)
    (history : List X) (s : OracleState X) :
    (uniformFunctionCompletion s).map (fun f => run A f fuel history) =
      (runLazy A rfStep fuel history s).map Prod.fst := by
  induction fuel generalizing history s with
  | zero =>
      rw [show (fun f : X → X => run A f 0 history) =
          Function.const (X → X) [] by funext f; rfl,
        PMF.map_const]
      simp [runLazy, PMF.pure_map]
  | succ fuel ih =>
      cases hA : A history with
      | none =>
          rw [show (fun f : X → X => run A f (fuel + 1) history) =
              Function.const (X → X) [] by funext f; simp [run, hA],
            PMF.map_const]
          simp [runLazy, hA, PMF.pure_map]
      | some x =>
          cases hx : s.table x with
          | some y =>
              have hpoint : ∀ f, uniformFunctionCompletion s f ≠ 0 →
                  run A f (fuel + 1) history =
                    (x, y) :: run A f fuel (history ++ [y]) := by
                intro f hf
                have hfmem : f ∈ functionCompletions s := by
                  by_contra hn
                  exact hf (by simp [uniformFunctionCompletion,
                    PMF.uniformOfFinset_apply, hn])
                have hfx : f x = y :=
                  ((mem_functionCompletions_iff s f).mp hfmem) x y hx
                simp [run, hA, hfx]
              rw [pmf_map_congr_support _ _ _ hpoint]
              rw [show (uniformFunctionCompletion s).map
                    (fun f => (x, y) :: run A f fuel (history ++ [y])) =
                  ((uniformFunctionCompletion s).map
                    (fun f => run A f fuel (history ++ [y]))).map
                      (fun tr => (x, y) :: tr) by
                    rw [PMF.map_comp]
                    rfl]
              rw [ih]
              simp only [runLazy, hA, rfStep, hx, PMF.pure_bind,
                PMF.map_comp]
              rfl
          | none =>
              rw [← uniformFunctionCompletion_fresh s x hx, PMF.map_bind]
              simp_rw [show ∀ y : X,
                  (uniformFunctionCompletion (store s x y)).map
                      (fun f => run A f (fuel + 1) history) =
                    ((uniformFunctionCompletion (store s x y)).map
                      (fun f => run A f fuel (history ++ [y]))).map
                        (fun tr => (x, y) :: tr) by
                  intro y
                  rw [PMF.map_comp]
                  apply pmf_map_congr_support
                  intro f hf
                  have hfmem : f ∈ functionCompletions (store s x y) := by
                    by_contra hn
                    exact hf (by simp [uniformFunctionCompletion,
                      PMF.uniformOfFinset_apply, hn])
                  have hfy : f x = y :=
                    ((mem_functionCompletions_store_iff s x y hx f).mp hfmem).2
                  simp [run, hA, hfy]]
              simp_rw [ih]
              simp [runLazy, hA, rfStep, hx, PMF.map_bind, PMF.map_comp]
              apply congrArg (fun k : X → PMF (Transcript X X) =>
                (PMF.uniformOfFintype X).bind k)
              funext y
              apply congrArg (fun g =>
                (runLazy A rfStep fuel (history ++ [y]) (store s x y)).map g)
              funext out
              rfl

/-- Whole uniformly sampled functions and the lazy RF have identical transcripts. -/
theorem prfTranscripts_eq_visible_lazyRF (A : QueryStrategy X X) (q : ℕ) :
    prfTranscripts X A q = visible (lazyRF A q) := by
  rw [prfTranscripts, transcriptPMF, ← uniformFunctionCompletion_initial]
  exact completionTranscripts_eq_lazyRF A q [] (initialState X)

end PRPPRFSwitching.Lazy
