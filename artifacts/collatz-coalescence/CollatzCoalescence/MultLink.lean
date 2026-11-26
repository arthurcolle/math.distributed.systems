import CollatzCoalescence.MultChain
import CollatzCoalescence.Link

/-!
# The link between residue classes and the pair chain, for a general odd multiplier

`mergedA a s k` is the set of residues `p` mod `2^k` on whose whole class the pair
`(x, a^d x + μ)` has merged after `k` steps of `Ta a`.  Its cardinality satisfies the transfer
recursion of the chain `stepA a`:

* `card_mergedA_zero`: `#(mergedA a s 0) = 1` if `s` is the absorbed state and `0` otherwise
  (for `a ≠ 1`, in particular for `2 ≤ a`);
* `card_mergedA_succ`: for odd `a`,
  `#(mergedA a s (k+1)) = #(mergedA a (stepA a s false) k) + #(mergedA a (stepA a s true) k)`.

This is `Link.lean` with `3` replaced by `a`.
-/

namespace Coalescence.Mult

open Classical in
/-- Residues `p` mod `2^k` on whose whole class the pair `(x, a^d x + μ)` has merged after `k` steps of `Ta a`. -/
noncomputable def mergedA (a : ℕ) (s : State) (k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ k)).filter fun p =>
    ∀ t : ℤ, (Ta a)^[k] ((p : ℤ) + 2 ^ k * t) = (Ta a)^[k] ((a : ℤ) ^ s.d * ((p : ℤ) + 2 ^ k * t) + s.mu)

/-- The pair `(P, a^d P + μ)` has merged after `k` steps of `Ta a`. -/
def PhiA (a : ℕ) (s : State) (k : ℕ) (P : ℤ) : Prop :=
  (Ta a)^[k] P = (Ta a)^[k] ((a : ℤ) ^ s.d * P + s.mu)

/-- The whole class of `x` mod `2^k` has merged after `k` steps of `Ta a`. -/
def GoodA (a : ℕ) (s : State) (k : ℕ) (x : ℤ) : Prop := ∀ t : ℤ, PhiA a s k (x + 2 ^ k * t)

theorem mem_mergedA (a : ℕ) (s : State) (k p : ℕ) :
    p ∈ mergedA a s k ↔ p < 2 ^ k ∧ GoodA a s k p := by
  simp only [mergedA, Finset.mem_filter, Finset.mem_range]
  rfl

/-! ### `GoodA` is a property of the residue class -/

theorem goodA_add_mul (a : ℕ) (s : State) (k : ℕ) (x u : ℤ) :
    GoodA a s k (x + 2 ^ k * u) ↔ GoodA a s k x := by
  constructor
  · intro H t
    have h := H (t - u)
    rwa [show x + 2 ^ k * u + 2 ^ k * (t - u) = x + 2 ^ k * t by ring] at h
  · intro H t
    have h := H (u + t)
    rwa [show x + 2 ^ k * (u + t) = x + 2 ^ k * u + 2 ^ k * t by ring] at h

theorem goodA_emod (a : ℕ) (s : State) (k : ℕ) (x : ℤ) :
    GoodA a s k (x % 2 ^ k) ↔ GoodA a s k x := by
  have e : x = x % 2 ^ k + 2 ^ k * (x / 2 ^ k) := (Int.emod_add_mul_ediv x (2 ^ k)).symm
  conv_rhs => rw [e]
  exact (goodA_add_mul a s k _ _).symm

/-! ### Affine structure of `(Ta a)^[k]` on a class mod `2^k` -/

theorem Ta_add_two_mul (a r m : ℤ) :
    Ta a (r + 2 * m) = Ta a r + (if r % 2 = 0 then 1 else a) * m := by
  unfold Ta
  have e : a * (r + 2 * m) + 1 = (a * r + 1) + 2 * (a * m) := by ring
  split_ifs <;> omega

/-- Number of odd terms among `x, Ta a x, …, (Ta a)^[k-1] x`. -/
def oddCountA (a : ℤ) : ℕ → ℤ → ℕ
  | 0, _ => 0
  | k + 1, x => (if x % 2 = 0 then 0 else 1) + oddCountA a k (Ta a x)

theorem Ta_iterate_add (a : ℤ) (k : ℕ) (x t : ℤ) :
    (Ta a)^[k] (x + 2 ^ k * t) = (Ta a)^[k] x + a ^ oddCountA a k x * t := by
  induction k generalizing x t with
  | zero => simp [oddCountA]
  | succ k ih =>
    have e : x + 2 ^ (k + 1) * t = x + 2 * (2 ^ k * t) := by ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, e, Ta_add_two_mul]
    by_cases hx : x % 2 = 0
    · simp only [if_pos hx, one_mul, oddCountA, zero_add]
      exact ih (Ta a x) t
    · simp only [if_neg hx, oddCountA]
      have e' : Ta a x + a * (2 ^ k * t) = Ta a x + 2 ^ k * (a * t) := by ring
      rw [e', ih (Ta a x) (a * t)]
      ring

/-- If the merging condition holds along a progression `y + 2^k g ℤ` with `g ≠ 0`, it holds on
the whole class of `y` mod `2^k`: the difference of the two orbits is affine in the class
parameter. -/
theorem goodA_of_thin (a : ℕ) (s : State) (k : ℕ) (y g : ℤ) (hg : g ≠ 0)
    (H : ∀ t : ℤ, PhiA a s k (y + 2 ^ k * (g * t))) : GoodA a s k y := by
  have e1 : ∀ t : ℤ, (Ta a)^[k] (y + 2 ^ k * t)
      = (Ta a)^[k] y + (a : ℤ) ^ oddCountA a k y * t :=
    Ta_iterate_add a k y
  have e2 : ∀ t : ℤ, (Ta a)^[k] ((a : ℤ) ^ s.d * (y + 2 ^ k * t) + s.mu)
      = (Ta a)^[k] ((a : ℤ) ^ s.d * y + s.mu)
        + (a : ℤ) ^ oddCountA a k ((a : ℤ) ^ s.d * y + s.mu) * ((a : ℤ) ^ s.d * t) := by
    intro t
    rw [← Ta_iterate_add]
    congr 1
    ring
  have h0 := H 0
  have h1 := H 1
  unfold PhiA at h0 h1
  rw [e1, e2] at h0 h1
  have hβ : ((a : ℤ) ^ oddCountA a k y
      - (a : ℤ) ^ oddCountA a k ((a : ℤ) ^ s.d * y + s.mu) * (a : ℤ) ^ s.d) * g = 0 := by
    linear_combination h1 - h0
  have hβ' := (mul_eq_zero.mp hβ).resolve_right hg
  intro t
  unfold PhiA
  rw [e1, e2]
  linear_combination h0 + t * hβ'

/-! ### One step: the orientation of `stepA_rel` does not depend on the point -/

theorem natCast_pow_emod_two (a : ℕ) (ha : a % 2 = 1) (d : ℕ) : (a : ℤ) ^ d % 2 = 1 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [pow_succ, Int.mul_emod, ih]
    omega

/-- On the parity class `x = 2u + c`, the condition "merged after `k+1` steps from state `s`" is
the condition "merged after `k` steps from state `stepA a s c`" at a point `g u + h` depending
affinely on `u`, with odd slope.  The one-step lemma of the chain enters as the hypothesis
`hrel`. -/
theorem stepA_affine_of_rel (a : ℕ) (ha : a % 2 = 1)
    (hrel : ∀ (s : State) (p q : ℤ), RelA a s p q →
      RelA a (stepA a s (decide (p % 2 = 1))) (Ta a p) (Ta a q) ∨
        RelA a (stepA a s (decide (p % 2 = 1))) (Ta a q) (Ta a p))
    (s : State) (c : Bool) :
    ∃ g h : ℤ, g % 2 = 1 ∧ ∀ (k : ℕ) (u : ℤ),
      PhiA a s (k + 1) (2 * u + (c.toNat : ℤ)) ↔ PhiA a (stepA a s c) k (g * u + h) := by
  -- `Ta a x` is affine in `u`
  obtain ⟨α, β, hα, hαβ⟩ : ∃ α β : ℤ, α % 2 = 1 ∧
      ∀ u : ℤ, Ta a (2 * u + (c.toNat : ℤ)) = α * u + β := by
    refine ⟨if (c.toNat : ℤ) % 2 = 0 then 1 else (a : ℤ), Ta a (c.toNat : ℤ), ?_, fun u => ?_⟩
    · split_ifs <;> omega
    · rw [show 2 * u + (c.toNat : ℤ) = (c.toNat : ℤ) + 2 * u by ring, Ta_add_two_mul]
      ring
  -- `Ta a q` is affine in `u`
  obtain ⟨A, B, hA, hAB⟩ : ∃ A B : ℤ, A % 2 = 1 ∧
      ∀ u : ℤ, Ta a ((a : ℤ) ^ s.d * (2 * u + (c.toNat : ℤ)) + s.mu) = A * u + B := by
    refine ⟨(if ((a : ℤ) ^ s.d * (c.toNat : ℤ) + s.mu) % 2 = 0 then 1 else (a : ℤ)) * (a : ℤ) ^ s.d,
      Ta a ((a : ℤ) ^ s.d * (c.toNat : ℤ) + s.mu), ?_, fun u => ?_⟩
    · have h3 := natCast_pow_emod_two a ha s.d
      have h3' := natCast_pow_emod_two a ha (s.d + 1)
      split_ifs
      · omega
      · rw [← pow_succ']
        exact h3'
    · rw [show (a : ℤ) ^ s.d * (2 * u + (c.toNat : ℤ)) + s.mu
          = ((a : ℤ) ^ s.d * (c.toNat : ℤ) + s.mu) + 2 * ((a : ℤ) ^ s.d * u) by ring,
        Ta_add_two_mul]
      ring
  -- the orientation of `hrel` is the same at every `u`
  have R : ∀ u : ℤ, A * u + B = (a : ℤ) ^ (stepA a s c).d * (α * u + β) + (stepA a s c).mu ∨
      α * u + β = (a : ℤ) ^ (stepA a s c).d * (A * u + B) + (stepA a s c).mu := by
    intro u
    have h := hrel s (2 * u + (c.toNat : ℤ))
      ((a : ℤ) ^ s.d * (2 * u + (c.toNat : ℤ)) + s.mu) rfl
    rw [decide_bit, hαβ, hAB] at h
    exact h
  rcases affine_dichotomy α β A B _ _ R with H | H
  · refine ⟨α, β, hα, fun k u => ?_⟩
    unfold PhiA
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hαβ, hAB, H u]
  · refine ⟨A, B, hA, fun k u => ?_⟩
    unfold PhiA
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hαβ, hAB, H u]
    exact eq_comm

/-! ### Counting -/

theorem goodA_succ_iff (a : ℕ) (s : State) (c : Bool) (g h : ℤ) (hg : g % 2 = 1) (k : ℕ)
    (H : ∀ u : ℤ, PhiA a s (k + 1) (2 * u + (c.toNat : ℤ)) ↔ PhiA a (stepA a s c) k (g * u + h))
    (p' : ℕ) :
    GoodA a s (k + 1) ((2 * p' + c.toNat : ℕ) : ℤ) ↔ GoodA a (stepA a s c) k (sig k g h p') := by
  rw [sig_cast, goodA_emod]
  have key : ∀ t : ℤ, PhiA a s (k + 1) (((2 * p' + c.toNat : ℕ) : ℤ) + 2 ^ (k + 1) * t) ↔
      PhiA a (stepA a s c) k (g * (p' : ℤ) + h + 2 ^ k * (g * t)) := by
    intro t
    have e1 : ((2 * p' + c.toNat : ℕ) : ℤ) + 2 ^ (k + 1) * t
        = 2 * ((p' : ℤ) + 2 ^ k * t) + (c.toNat : ℤ) := by
      push_cast
      ring
    have e2 : g * (p' : ℤ) + h + 2 ^ k * (g * t) = g * ((p' : ℤ) + 2 ^ k * t) + h := by ring
    rw [e1, e2]
    exact H _
  constructor
  · intro G
    apply goodA_of_thin _ _ _ _ g (by omega)
    intro t
    exact (key t).mp (G t)
  · intro G t
    exact (key t).mpr (G (g * t))

/-- The residues of parity `c` in `mergedA a s (k+1)` are in bijection with
`mergedA a (stepA a s c) k`. -/
theorem card_parityA_of_rel (a : ℕ) (ha : a % 2 = 1)
    (hrel : ∀ (s : State) (p q : ℤ), RelA a s p q →
      RelA a (stepA a s (decide (p % 2 = 1))) (Ta a p) (Ta a q) ∨
        RelA a (stepA a s (decide (p % 2 = 1))) (Ta a q) (Ta a p))
    (s : State) (k : ℕ) (c : Bool) :
    ((mergedA a s (k + 1)).filter (fun p => p % 2 = c.toNat)).card
      = (mergedA a (stepA a s c) k).card := by
  obtain ⟨g, h, hg, H⟩ := stepA_affine_of_rel a ha hrel s c
  have hc : c.toNat ≤ 1 := Bool.toNat_le c
  apply Finset.card_bij (fun p _ => sig k g h (p / 2))
  · intro p hp
    rw [Finset.mem_filter, mem_mergedA] at hp
    obtain ⟨⟨_, hG⟩, hpar⟩ := hp
    rw [mem_mergedA]
    refine ⟨sig_lt k g h _, ?_⟩
    have e : 2 * (p / 2) + c.toNat = p := by omega
    have hG' : GoodA a s (k + 1) ((2 * (p / 2) + c.toNat : ℕ) : ℤ) := by
      rw [e]
      exact hG
    exact (goodA_succ_iff a s c g h hg k (H k) (p / 2)).mp hG'
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_filter, mem_mergedA] at hp₁ hp₂
    have hlt₁ := hp₁.1.1
    have hlt₂ := hp₂.1.1
    rw [pow_succ] at hlt₁ hlt₂
    have h1 : p₁ / 2 < 2 ^ k := by omega
    have h2 : p₂ / 2 < 2 ^ k := by omega
    have h3 := sig_inj k g h hg h1 h2 heq
    omega
  · intro b hb
    rw [mem_mergedA] at hb
    obtain ⟨r, hr, rfl⟩ := sig_surj k g h hg b hb.1
    refine ⟨2 * r + c.toNat, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_mergedA]
      refine ⟨⟨by rw [pow_succ]; omega, ?_⟩, by omega⟩
      exact (goodA_succ_iff a s c g h hg k (H k) r).mpr hb.2
    · have e : (2 * r + c.toNat) / 2 = r := by omega
      show sig k g h ((2 * r + c.toNat) / 2) = sig k g h r
      rw [e]

theorem card_mergedA_succ_of_rel (a : ℕ) (ha : a % 2 = 1)
    (hrel : ∀ (s : State) (p q : ℤ), RelA a s p q →
      RelA a (stepA a s (decide (p % 2 = 1))) (Ta a p) (Ta a q) ∨
        RelA a (stepA a s (decide (p % 2 = 1))) (Ta a q) (Ta a p))
    (s : State) (k : ℕ) :
    (mergedA a s (k + 1)).card
      = (mergedA a (stepA a s false) k).card + (mergedA a (stepA a s true) k).card := by
  rw [← card_parityA_of_rel a ha hrel s k false, ← card_parityA_of_rel a ha hrel s k true]
  have hsplit : mergedA a s (k + 1)
      = (mergedA a s (k + 1)).filter (fun p => p % 2 = false.toNat)
        ∪ (mergedA a s (k + 1)).filter (fun p => p % 2 = true.toNat) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Bool.toNat_false, Bool.toNat_true]
    constructor
    · intro hp
      rcases Nat.mod_two_eq_zero_or_one p with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint ((mergedA a s (k + 1)).filter (fun p => p % 2 = false.toNat))
      ((mergedA a s (k + 1)).filter (fun p => p % 2 = true.toNat)) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    simp only [Bool.toNat_false, Bool.toNat_true] at h1 h2
    omega
  conv_lhs => rw [hsplit]
  exact Finset.card_union_of_disjoint hdisj

/-! ### Headline statements -/

/-- The base case needs only `a ≠ 1` (for `a = 1` every state `(d, 0)` is merged at time `0`). -/
theorem card_mergedA_zero_of_ne_one (a : ℕ) (ha : a ≠ 1) (s : State) :
    (mergedA a s 0).card = if s = absorbed then 1 else 0 := by
  split_ifs with hs
  · subst hs
    have hm : mergedA a absorbed 0 = {0} := by
      ext p
      rw [mem_mergedA, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, _⟩
        simpa using hp
      · rintro rfl
        refine ⟨by norm_num, fun t => ?_⟩
        simp [PhiA, absorbed]
    rw [hm]
    rfl
  · have hm : mergedA a s 0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rw [mem_mergedA] at hp
      obtain ⟨hp0, hG⟩ := hp
      have hp0' : p = 0 := by simpa using hp0
      subst hp0'
      obtain ⟨d, μ⟩ := s
      have h0 : ((0 : ℕ) : ℤ) + 2 ^ 0 * 0 = (a : ℤ) ^ d * (((0 : ℕ) : ℤ) + 2 ^ 0 * 0) + μ := hG 0
      have h1 : ((0 : ℕ) : ℤ) + 2 ^ 0 * 1 = (a : ℤ) ^ d * (((0 : ℕ) : ℤ) + 2 ^ 0 * 1) + μ := hG 1
      rw [Nat.cast_zero, pow_zero, mul_zero, add_zero, mul_zero, zero_add] at h0
      rw [Nat.cast_zero, pow_zero, mul_one, zero_add, mul_one] at h1
      have hμ : μ = 0 := h0.symm
      have hd : d = 0 := by
        rw [hμ, add_zero] at h1
        have h1n : a ^ d = 1 := by exact_mod_cast h1.symm
        rcases Nat.pow_eq_one.mp h1n with h | h
        · exact absurd h ha
        · exact h
      exact hs (by rw [hμ, hd]; rfl)
    rw [hm]
    rfl

theorem card_mergedA_zero (a : ℕ) (ha : 2 ≤ a) (s : State) :
    (mergedA a s 0).card = if s = absorbed then 1 else 0 :=
  card_mergedA_zero_of_ne_one a (by omega) s

theorem card_mergedA_succ (a : ℕ) (ha : a % 2 = 1) (s : State) (k : ℕ) :
    (mergedA a s (k + 1)).card = (mergedA a (stepA a s false) k).card + (mergedA a (stepA a s true) k).card :=
  card_mergedA_succ_of_rel a ha (stepA_rel a ha) s k

end Coalescence.Mult

#print axioms Coalescence.Mult.card_mergedA_zero
#print axioms Coalescence.Mult.card_mergedA_succ
