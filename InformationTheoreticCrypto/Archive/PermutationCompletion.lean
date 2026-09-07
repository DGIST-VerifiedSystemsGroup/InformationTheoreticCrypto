import InformationTheoreticCrypto.Archive.FunctionCompletion

/-! # Completing a lazy random-permutation table -/

namespace PRPPRFSwitching.Lazy

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]

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

@[simp]
theorem permutationCompletions_initial :
    permutationCompletions (initialState X) = Finset.univ := by
  ext p
  simp [permutationCompletions, PermutationCompatible]

theorem permutationCompatible_store_iff (s : OracleState X) (x y : X)
    (hx : s.table x = none) (p : Equiv.Perm X) :
    PermutationCompatible (store s x y) p ↔
      PermutationCompatible s p ∧ p x = y := by
  constructor
  · intro h
    constructor
    · intro z w hzw
      have hzx : z ≠ x := by
        intro hz
        subst z
        rw [hx] at hzw
        contradiction
      exact h z w (by simpa only [store_lookup_of_ne s hzx] using hzw)
    · exact h x y (store_lookup_same s x y)
  · rintro ⟨hs, hxy⟩ z w hzw
    by_cases hzx : z = x
    · subst z
      simp only [store_lookup_same] at hzw
      cases hzw
      exact hxy
    · rw [store_lookup_of_ne s hzx] at hzw
      exact hs z w hzw

noncomputable def permutationCompletionFiber
    (s : OracleState X) (x y : X) : Finset (Equiv.Perm X) :=
  (permutationCompletions s).filter fun p => p x = y

theorem mem_permutationCompletionFiber_iff
    (s : OracleState X) (x y : X) (p : Equiv.Perm X) :
    p ∈ permutationCompletionFiber s x y ↔
      p ∈ permutationCompletions s ∧ p x = y := by
  simp [permutationCompletionFiber]

theorem permutationCompletions_store_eq_fiber
    (s : OracleState X) (x y : X) (hx : s.table x = none) :
    permutationCompletions (store s x y) =
      permutationCompletionFiber s x y := by
  ext p
  simp [mem_permutationCompletions_iff, mem_permutationCompletionFiber_iff,
    permutationCompatible_store_iff s x y hx p]

/-- Postcompose a permutation with the transposition of two outputs. -/
def swapOutputs (y₁ y₂ : X) (p : Equiv.Perm X) : Equiv.Perm X :=
  p.trans (Equiv.swap y₁ y₂)

@[simp]
theorem swapOutputs_apply (y₁ y₂ : X) (p : Equiv.Perm X) (x : X) :
    swapOutputs y₁ y₂ p x = Equiv.swap y₁ y₂ (p x) := rfl

theorem permutationCompatible_swapOutputs (s : OracleState X)
    (hs : CoversTable s) {y₁ y₂ : X}
    (hy₁ : y₁ ∈ availableOutputs s) (hy₂ : y₂ ∈ availableOutputs s)
    {p : Equiv.Perm X} (hp : PermutationCompatible s p) :
    PermutationCompatible s (swapOutputs y₁ y₂ p) := by
  intro z w hzw
  have hwused : w ∈ s.usedOutputs := hs hzw
  have hwy₁ : w ≠ y₁ := by
    intro h
    subst w
    exact (mem_availableOutputs_iff s y₁).mp hy₁ hwused
  have hwy₂ : w ≠ y₂ := by
    intro h
    subst w
    exact (mem_availableOutputs_iff s y₂).mp hy₂ hwused
  rw [swapOutputs_apply, hp z w hzw]
  simp [Equiv.swap_apply_of_ne_of_ne hwy₁ hwy₂]

/-- Swapping two still-available outputs bijects the corresponding completion
fibers.  This is the finite permutation analogue of changing one fresh
coordinate of a total function. -/
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
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (permutationCompletionFiberEquiv s hs x y₁ y₂ hy₁ hy₂)

theorem compatible_fresh_image_available (s : OracleState X)
    (hexact : ExactUsed s) (hinj : InjectiveTable s)
    {p : Equiv.Perm X} (hp : PermutationCompatible s p)
    {x : X} (hx : s.table x = none) :
    p x ∈ availableOutputs s := by
  rw [mem_availableOutputs_iff]
  intro hused
  obtain ⟨z, hz⟩ := (hexact (p x)).mp hused
  have hpz : p z = p x := hp z (p x) hz
  have hzx : z = x := p.injective hpz
  subst z
  rw [hx] at hz
  contradiction

theorem permutationCompletions_store_nonempty (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (x y : X) (hx : s.table x = none)
    (hy : y ∈ availableOutputs s) :
    (permutationCompletions (store s x y)).Nonempty := by
  obtain ⟨p, hp⟩ := hcomp
  have hpcompat := (mem_permutationCompletions_iff s p).mp hp
  have hpx : p x ∈ availableOutputs s :=
    compatible_fresh_image_available s hexact hinj hpcompat hx
  rw [permutationCompletions_store_eq_fiber s x y hx]
  exact ⟨swapOutputs (p x) y p, by
    rw [mem_permutationCompletionFiber_iff]
    refine ⟨(mem_permutationCompletions_iff s _).mpr
      (permutationCompatible_swapOutputs s hs hpx hy hpcompat), ?_⟩
    simp [swapOutputs]⟩

/-- A fresh input partitions compatible permutations into equally-sized fibers,
one for each output not used by the partial table. -/
theorem card_permutationCompletions_eq_mul_fiber (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (x y : X) (hx : s.table x = none)
    (hy : y ∈ availableOutputs s) :
    (permutationCompletions s).card =
      (availableOutputs s).card * (permutationCompletionFiber s x y).card := by
  classical
  calc
    (permutationCompletions s).card =
        ∑ z ∈ availableOutputs s,
          ((permutationCompletions s).filter fun p => p x = z).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact compatible_fresh_image_available s hexact hinj
        ((mem_permutationCompletions_iff s p).mp hp) hx
    _ = ∑ z ∈ availableOutputs s,
          (permutationCompletionFiber s x z).card := by
      rfl
    _ = ∑ _z ∈ availableOutputs s,
          (permutationCompletionFiber s x y).card := by
      apply Finset.sum_congr rfl
      intro z hz
      exact card_permutationCompletionFiber_eq s hs x z y hz hy
    _ = (availableOutputs s).card *
          (permutationCompletionFiber s x y).card := by simp

noncomputable def uniformPermutationCompletion (s : OracleState X)
    (h : (permutationCompletions s).Nonempty) : PMF (Equiv.Perm X) :=
  PMF.uniformOfFinset (permutationCompletions s) h

@[simp]
theorem uniformPermutationCompletion_initial :
    (uniformPermutationCompletion (initialState X) (by simp)).map
        (fun p : Equiv.Perm X => (p : X → X)) =
      randomPermutation X := by
  have hu : uniformPermutationCompletion (initialState X) (by simp) =
      PMF.uniformOfFintype (Equiv.Perm X) := by
    apply PMF.ext
    intro p
    simp [uniformPermutationCompletion, permutationCompletions_initial,
      PMF.uniformOfFintype_apply]
  rw [hu]
  change PMF.map (fun p : Equiv.Perm X => (p : X → X))
      (PMF.uniformOfFintype (Equiv.Perm X)) =
    PMF.map id (PMF.map (fun p : Equiv.Perm X => (p : X → X))
      (PMF.uniformOfFintype (Equiv.Perm X)))
  rw [PMF.map_id]

noncomputable def permutationCompletionAfter (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (x : X) (hx : s.table x = none) (y : X) : PMF (Equiv.Perm X) :=
  if hy : y ∈ availableOutputs s then
    uniformPermutationCompletion (store s x y)
      (permutationCompletions_store_nonempty s hs hexact hinj hcomp x y hx hy)
  else
    PMF.pure 1

/-- Deferred decisions for a random permutation: conditioned on the current
partial table, a fresh image is uniform among precisely the unused outputs. -/
theorem uniformPermutationCompletion_fresh (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (x : X) (hx : s.table x = none)
    (havailable : (availableOutputs s).Nonempty) :
    (PMF.uniformOfFinset (availableOutputs s) havailable).bind
        (permutationCompletionAfter s hs hexact hinj hcomp x hx) =
      uniformPermutationCompletion s hcomp := by
  classical
  apply PMF.ext
  intro p
  rw [PMF.bind_apply, tsum_fintype]
  simp only [permutationCompletionAfter, uniformPermutationCompletion,
    PMF.uniformOfFinset_apply]
  by_cases hp : p ∈ permutationCompletions s
  · have hpcompat := (mem_permutationCompletions_iff s p).mp hp
    have hpx : p x ∈ availableOutputs s :=
      compatible_fresh_image_available s hexact hinj hpcompat hx
    have hmem : ∀ y : X,
        (p ∈ permutationCompletions (store s x y)) ↔ p x = y := by
      intro y
      rw [permutationCompletions_store_eq_fiber s x y hx,
        mem_permutationCompletionFiber_iff]
      simp [hp]
    have hcard : ∀ y ∈ availableOutputs s,
        (permutationCompletions (store s x y)).card =
          (permutationCompletionFiber s x (p x)).card := by
      intro y hy
      rw [permutationCompletions_store_eq_fiber s x y hx]
      exact card_permutationCompletionFiber_eq s hs x y (p x) hy hpx
    rw [Fintype.sum_eq_single (p x)]
    · simp only [hpx, ↓reduceIte, permutationCompletionAfter, dif_pos,
        uniformPermutationCompletion, PMF.uniformOfFinset_apply,
        (hmem (p x)).mpr rfl, hp, if_true]
      rw [hcard (p x) hpx,
        card_permutationCompletions_eq_mul_fiber s hs hexact hinj x (p x) hx hpx]
      push_cast
      rw [ENNReal.mul_inv (by left; simpa using
        Finset.card_ne_zero.mpr havailable) (by left; simp)]
    · intro y hne
      by_cases hy : y ∈ availableOutputs s
      · simp [permutationCompletionAfter, hy, uniformPermutationCompletion,
          PMF.uniformOfFinset_apply, hmem y, hne, Ne.symm hne]
      · simp [hy]
  · have hnone : ∀ y : X, p ∉ permutationCompletions (store s x y) := by
      intro y hpy
      apply hp
      rw [mem_permutationCompletions_iff]
      exact ((permutationCompatible_store_iff s x y hx p).mp
        ((mem_permutationCompletions_iff _ _).mp hpy)).1
    simp [hp]
    intro y hy
    simp [permutationCompletionAfter, hy, uniformPermutationCompletion,
      PMF.uniformOfFinset_apply, hnone y]

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

/-- Evaluating a uniformly random total permutation compatible with the
current table gives the same adaptive transcript as lazy permutation
sampling.  The capacity premise is the only reason this statement is
restricted to at most `|X|` remaining fresh steps. -/
theorem completionTranscripts_eq_lazyRP (A : QueryStrategy X X) (fuel : ℕ)
    (history : List X) (s : OracleState X)
    (hs : CoversTable s) (hexact : ExactUsed s) (hinj : InjectiveTable s)
    (hcomp : (permutationCompletions s).Nonempty)
    (hcap : s.usedOutputs.card + fuel ≤ Fintype.card X) :
    (uniformPermutationCompletion s hcomp).map
        (fun p => run A (fun x => p x) fuel history) =
      (runLazy A rpStep fuel history s).map Prod.fst := by
  induction fuel generalizing history s with
  | zero =>
      rw [show (fun p : Equiv.Perm X => run A (fun x => p x) 0 history) =
          Function.const (Equiv.Perm X) [] by funext p; rfl,
        PMF.map_const]
      simp [runLazy, PMF.pure_map]
  | succ fuel ih =>
      cases hA : A history with
      | none =>
          rw [show (fun p : Equiv.Perm X =>
                run A (fun x => p x) (fuel + 1) history) =
              Function.const (Equiv.Perm X) [] by
                funext p; simp [run, hA],
            PMF.map_const]
          simp [runLazy, hA, PMF.pure_map]
      | some x =>
          cases hx : s.table x with
          | some y =>
              have hpoint : ∀ p, uniformPermutationCompletion s hcomp p ≠ 0 →
                  run A (fun z => p z) (fuel + 1) history =
                    (x, y) :: run A (fun z => p z) fuel (history ++ [y]) := by
                intro p hp
                have hpmem : p ∈ permutationCompletions s := by
                  by_contra hn
                  exact hp (by simp [uniformPermutationCompletion,
                    PMF.uniformOfFinset_apply, hn])
                have hpx : p x = y :=
                  ((mem_permutationCompletions_iff s p).mp hpmem) x y hx
                simp [run, hA, hpx]
              rw [pmf_map_congr_support _ _ _ hpoint]
              rw [show (uniformPermutationCompletion s hcomp).map
                    (fun p => (x, y) ::
                      run A (fun z => p z) fuel (history ++ [y])) =
                  ((uniformPermutationCompletion s hcomp).map
                    (fun p => run A (fun z => p z) fuel (history ++ [y]))).map
                      (fun tr => (x, y) :: tr) by
                    rw [PMF.map_comp]
                    rfl]
              rw [ih (history := history ++ [y]) (s := s) hs hexact hinj hcomp
                (by omega)]
              simp only [runLazy, hA, rpStep, hx, PMF.pure_bind, PMF.map_comp]
              rfl
          | none =>
              have hlt : s.usedOutputs.card < Fintype.card X := by omega
              have havail : (availableOutputs s).Nonempty :=
                availableOutputs_nonempty_of_card_lt s hlt
              rw [← uniformPermutationCompletion_fresh s hs hexact hinj hcomp x hx havail,
                PMF.map_bind]
              let sample := PMF.uniformOfFinset (availableOutputs s) havail
              let next : X → PMF (Transcript X X) := fun y =>
                (runLazy A rpStep fuel (history ++ [y]) (store s x y)).map
                  (fun out => (x, y) :: out.1)
              have hnext : ∀ y, sample y ≠ 0 →
                  (permutationCompletionAfter s hs hexact hinj hcomp x hx y).map
                      (fun p => run A (fun z => p z) (fuel + 1) history) =
                    next y := by
                intro y hyprob
                have hy : y ∈ availableOutputs s := by
                  by_contra hyn
                  exact hyprob (by simp [sample, PMF.uniformOfFinset_apply, hyn])
                have hynused : y ∉ s.usedOutputs :=
                  (mem_availableOutputs_iff s y).mp hy
                have hstore := permutationCompletions_store_nonempty s hs hexact hinj
                  hcomp x y hx hy
                simp only [permutationCompletionAfter, dif_pos hy]
                rw [show (uniformPermutationCompletion (store s x y) hstore).map
                      (fun p => run A (fun z => p z) (fuel + 1) history) =
                    ((uniformPermutationCompletion (store s x y) hstore).map
                      (fun p => run A (fun z => p z) fuel (history ++ [y]))).map
                        (fun tr => (x, y) :: tr) by
                    rw [PMF.map_comp]
                    apply pmf_map_congr_support
                    intro p hp
                    have hpmem : p ∈ permutationCompletions (store s x y) := by
                      by_contra hn
                      exact hp (by simp [uniformPermutationCompletion,
                        PMF.uniformOfFinset_apply, hn])
                    have hpy : p x = y :=
                      ((permutationCompatible_store_iff s x y hx p).mp
                        ((mem_permutationCompletions_iff _ _).mp hpmem)).2
                    simp [run, hA, hpy]]
                have hcardStore : (store s x y).usedOutputs.card + fuel ≤
                    Fintype.card X := by
                  simp only [store_usedOutputs, Finset.card_insert_of_notMem hynused]
                  omega
                rw [ih (history := history ++ [y]) (s := store s x y)
                  (store_covers s x y hs) (store_exactUsed s x y hx hexact)
                  (store_injective s x y hinj hx hynused hs) hstore hcardStore]
                rw [PMF.map_comp]
                rfl
              rw [pmf_bind_congr_support sample _ next hnext]
              simp [sample, next, runLazy, hA, rpStep, hx, havail,
                PMF.map_bind, PMF.map_comp]
              apply congrArg (fun k : X → PMF (Transcript X X) =>
                (PMF.uniformOfFinset (availableOutputs s) _).bind k)
              funext y
              apply congrArg (fun g =>
                (runLazy A rpStep fuel (history ++ [y]) (store s x y)).map g)
              funext out
              rfl

/-- Whole uniformly sampled permutations and the lazy RP have identical
transcripts for every query bound not exceeding the domain size. -/
theorem prpTranscripts_eq_visible_lazyRP (A : QueryStrategy X X) (q : ℕ)
    (hq : q ≤ Fintype.card X) :
    prpTranscripts X A q = visible (lazyRP A q) := by
  rw [prpTranscripts, transcriptPMF, ← uniformPermutationCompletion_initial]
  rw [PMF.map_comp]
  exact completionTranscripts_eq_lazyRP A q [] (initialState X)
    initialState_covers initialState_exactUsed initialState_injective (by simp)
    (by simpa using hq)

theorem eventProbability_le_one (p : PMF Ω) (decision : Ω → Bool) :
    eventProbability p decision ≤ 1 := by
  have h := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
    (PMF.coe_le_one (p.map decision) true)
  simpa [eventProbability] using h

theorem advantage_le_one (p₁ p₂ : PMF Ω) (decision : Ω → Bool) :
    advantage p₁ p₂ decision ≤ 1 := by
  rw [advantage]
  apply abs_sub_le_iff.mpr
  have h₁nonneg : 0 ≤ eventProbability p₁ decision := ENNReal.toReal_nonneg
  have h₂nonneg : 0 ≤ eventProbability p₂ decision := ENNReal.toReal_nonneg
  have h₁ := eventProbability_le_one p₁ decision
  have h₂ := eventProbability_le_one p₂ decision
  constructor <;> linarith

/-- The whole-oracle statement advertised by `SwitchingBound`.  For the
nontrivial range it is transported through the two lazy-sampling equivalences;
beyond the domain size the birthday expression is already at least one. -/
theorem switchingBound_all (A : QueryStrategy X X) (q : ℕ) :
    SwitchingBound X A q := by
  intro decision
  by_cases hq : q ≤ Fintype.card X
  · rw [prfTranscripts_eq_visible_lazyRF A q,
      prpTranscripts_eq_visible_lazyRP A q hq]
    exact lazy_switching_bound A q hq decision
  · have hbad : advantage (prfTranscripts X A q) (prpTranscripts X A q)
        decision ≤ 1 := advantage_le_one _ _ decision
    have hNnat : 0 < Fintype.card X := Fintype.card_pos
    have hqnat : Fintype.card X + 1 ≤ q := by omega
    have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast hNnat
    have hN1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hNnat
    have hqreal : (Fintype.card X : ℝ) + 1 ≤ q := by exact_mod_cast hqnat
    have hone : (1 : ℝ) ≤
        (q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card X)).2
      have hq2 : (2 : ℝ) ≤ q := by nlinarith
      have hminus : (Fintype.card X : ℝ) ≤ (q : ℝ) - 1 := by nlinarith
      have hprod := mul_le_mul hq2 hminus (le_of_lt hN)
        (by positivity : (0 : ℝ) ≤ q)
      nlinarith
    exact le_trans hbad hone

end PRPPRFSwitching.Lazy
