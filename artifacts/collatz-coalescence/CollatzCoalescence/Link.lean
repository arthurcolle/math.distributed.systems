import CollatzCoalescence.Chain

/-!
# The link between residue classes and the pair chain

`merged s k` is the set of residues `p` mod `2^k` on whose whole class the pair
`(x, 3^d x + μ)` has merged after `k` steps of `T`.  The two headline statements say that its
cardinality satisfies the transfer recursion of the chain `step`:

* `card_merged_zero`: `#(merged s 0) = 1` if `s` is the absorbed state and `0` otherwise;
* `card_merged_succ`: `#(merged s (k+1)) = #(merged (step s false) k) + #(merged (step s true) k)`.

Hence `#(merged s k)` is the number of coin words of length `k` leading from `s` to the absorbed
state (the sentence after the One-step Lemma of `main.tex`).
-/

namespace Coalescence

open Classical in
/-- Residues `p` mod `2^k` on whose whole class the pair `(x, 3^d x + μ)` has merged after `k` steps. -/
noncomputable def merged (s : State) (k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ k)).filter fun p =>
    ∀ t : ℤ, T^[k] ((p : ℤ) + 2 ^ k * t) = T^[k] (3 ^ s.d * ((p : ℤ) + 2 ^ k * t) + s.mu)

/-- The pair `(P, 3^d P + μ)` has merged after `k` steps. -/
def Phi (s : State) (k : ℕ) (P : ℤ) : Prop := T^[k] P = T^[k] (3 ^ s.d * P + s.mu)

/-- The whole class of `x` mod `2^k` has merged after `k` steps. -/
def Good (s : State) (k : ℕ) (x : ℤ) : Prop := ∀ t : ℤ, Phi s k (x + 2 ^ k * t)

theorem mem_merged (s : State) (k p : ℕ) : p ∈ merged s k ↔ p < 2 ^ k ∧ Good s k p := by
  simp only [merged, Finset.mem_filter, Finset.mem_range]
  rfl

/-! ### `Good` is a property of the residue class -/

theorem good_add_mul (s : State) (k : ℕ) (x u : ℤ) :
    Good s k (x + 2 ^ k * u) ↔ Good s k x := by
  constructor
  · intro H t
    have h := H (t - u)
    rwa [show x + 2 ^ k * u + 2 ^ k * (t - u) = x + 2 ^ k * t by ring] at h
  · intro H t
    have h := H (u + t)
    rwa [show x + 2 ^ k * (u + t) = x + 2 ^ k * u + 2 ^ k * t by ring] at h

theorem good_emod (s : State) (k : ℕ) (x : ℤ) : Good s k (x % 2 ^ k) ↔ Good s k x := by
  have e : x = x % 2 ^ k + 2 ^ k * (x / 2 ^ k) := (Int.emod_add_mul_ediv x (2 ^ k)).symm
  conv_rhs => rw [e]
  exact (good_add_mul s k _ _).symm

/-! ### Affine structure of `T^[k]` on a class mod `2^k` -/

theorem T_add_two_mul (r m : ℤ) :
    T (r + 2 * m) = T r + (if r % 2 = 0 then 1 else 3) * m := by
  unfold T
  split_ifs <;> omega

/-- Number of odd terms among `x, T x, …, T^[k-1] x`. -/
def oddCount : ℕ → ℤ → ℕ
  | 0, _ => 0
  | k + 1, x => (if x % 2 = 0 then 0 else 1) + oddCount k (T x)

theorem T_iterate_add (k : ℕ) (x t : ℤ) :
    T^[k] (x + 2 ^ k * t) = T^[k] x + 3 ^ oddCount k x * t := by
  induction k generalizing x t with
  | zero => simp [oddCount]
  | succ k ih =>
    have e : x + 2 ^ (k + 1) * t = x + 2 * (2 ^ k * t) := by ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, e, T_add_two_mul]
    by_cases hx : x % 2 = 0
    · simp only [if_pos hx, one_mul, oddCount, zero_add]
      exact ih (T x) t
    · simp only [if_neg hx, oddCount]
      have e' : T x + 3 * (2 ^ k * t) = T x + 2 ^ k * (3 * t) := by ring
      rw [e', ih (T x) (3 * t)]
      ring

/-- If the merging condition holds along a progression `y + 2^k g ℤ` with `g ≠ 0`, it holds on
the whole class of `y` mod `2^k`: the difference of the two orbits is affine in the class
parameter. -/
theorem good_of_thin (s : State) (k : ℕ) (y g : ℤ) (hg : g ≠ 0)
    (H : ∀ t : ℤ, Phi s k (y + 2 ^ k * (g * t))) : Good s k y := by
  have e1 : ∀ t : ℤ, T^[k] (y + 2 ^ k * t) = T^[k] y + 3 ^ oddCount k y * t :=
    T_iterate_add k y
  have e2 : ∀ t : ℤ, T^[k] (3 ^ s.d * (y + 2 ^ k * t) + s.mu)
      = T^[k] (3 ^ s.d * y + s.mu)
        + 3 ^ oddCount k (3 ^ s.d * y + s.mu) * (3 ^ s.d * t) := by
    intro t
    rw [← T_iterate_add]
    congr 1
    ring
  have h0 := H 0
  have h1 := H 1
  unfold Phi at h0 h1
  rw [e1, e2] at h0 h1
  have hβ : ((3 : ℤ) ^ oddCount k y
      - 3 ^ oddCount k (3 ^ s.d * y + s.mu) * 3 ^ s.d) * g = 0 := by
    linear_combination h1 - h0
  have hβ' := (mul_eq_zero.mp hβ).resolve_right hg
  intro t
  unfold Phi
  rw [e1, e2]
  linear_combination h0 + t * hβ'

/-! ### Odd affine maps permute the residues mod `2^k` -/

/-- The affine map `p ↦ g p + h` on residues mod `2^k`. -/
def sig (k : ℕ) (g h : ℤ) (p : ℕ) : ℕ := ((g * p + h) % 2 ^ k).toNat

theorem sig_cast (k : ℕ) (g h : ℤ) (p : ℕ) :
    ((sig k g h p : ℕ) : ℤ) = (g * p + h) % 2 ^ k := by
  unfold sig
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

theorem sig_lt (k : ℕ) (g h : ℤ) (p : ℕ) : sig k g h p < 2 ^ k := by
  have h1 : (g * p + h) % 2 ^ k < 2 ^ k := Int.emod_lt_of_pos _ (by positivity)
  have h2 := sig_cast k g h p
  have h3 : ((sig k g h p : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    rw [h2]
    push_cast
    exact h1
  exact_mod_cast h3

theorem sig_inj (k : ℕ) (g h : ℤ) (hg : g % 2 = 1) {p p' : ℕ} (hp : p < 2 ^ k)
    (hp' : p' < 2 ^ k) (hpp : sig k g h p = sig k g h p') : p = p' := by
  have hpZ : (p : ℤ) < 2 ^ k := by exact_mod_cast hp
  have hpZ' : (p' : ℤ) < 2 ^ k := by exact_mod_cast hp'
  have h1 : (g * p + h) % 2 ^ k = (g * p' + h) % 2 ^ k := by
    rw [← sig_cast, ← sig_cast, hpp]
  have h2 : (2 ^ k : ℤ) ∣ (g * p' + h) - (g * p + h) := Int.ModEq.dvd h1
  have h3 : (2 ^ k : ℤ) ∣ ((p' : ℤ) - p) * g := by
    have e : (g * p' + h) - (g * p + h) = ((p' : ℤ) - p) * g := by ring
    rwa [e] at h2
  have hcop2 : IsCoprime (2 : ℤ) g := ⟨-(g / 2), 1, by omega⟩
  have hcop : IsCoprime ((2 : ℤ) ^ k) g := hcop2.pow_left
  have h4 : (2 ^ k : ℤ) ∣ (p' : ℤ) - p := hcop.dvd_of_dvd_mul_right h3
  have h5 : (p' : ℤ) - p = 0 :=
    Int.eq_zero_of_abs_lt_dvd h4 (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem sig_surj (k : ℕ) (g h : ℤ) (hg : g % 2 = 1) (b : ℕ) (hb : b < 2 ^ k) :
    ∃ a, a < 2 ^ k ∧ sig k g h a = b := by
  have hinj : Set.InjOn (sig k g h) (Finset.range (2 ^ k) : Set ℕ) := by
    intro p hp p' hp' hpp
    exact sig_inj k g h hg (Finset.mem_range.mp hp) (Finset.mem_range.mp hp') hpp
  have hsub : (Finset.range (2 ^ k)).image (sig k g h) ⊆ Finset.range (2 ^ k) := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (sig_lt k g h a)
  have heq : (Finset.range (2 ^ k)).image (sig k g h) = Finset.range (2 ^ k) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have hb' : b ∈ (Finset.range (2 ^ k)).image (sig k g h) := by
    rw [heq]
    exact Finset.mem_range.mpr hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb'
  exact ⟨a, Finset.mem_range.mp ha, rfl⟩

/-! ### One step: the orientation of `step_rel` does not depend on the point -/

theorem aff_ext (a b A B D M : ℤ) {u v : ℤ} (huv : u ≠ v)
    (hu : A * u + B = D * (a * u + b) + M) (hv : A * v + B = D * (a * v + b) + M) (w : ℤ) :
    A * w + B = D * (a * w + b) + M := by
  have h : (A - D * a) * (u - v) = 0 := by linear_combination hu - hv
  have hp : A - D * a = 0 := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr huv)
  linear_combination hu + (w - u) * hp

/-- Two affine functions related, at each point, in one of two affine ways are related in the
same way at every point. -/
theorem affine_dichotomy (a b A B D M : ℤ)
    (R : ∀ u : ℤ, A * u + B = D * (a * u + b) + M ∨ a * u + b = D * (A * u + B) + M) :
    (∀ u : ℤ, A * u + B = D * (a * u + b) + M) ∨
      (∀ u : ℤ, a * u + b = D * (A * u + B) + M) := by
  have h01 : (0 : ℤ) ≠ 1 := by norm_num
  have h02 : (0 : ℤ) ≠ 2 := by norm_num
  have h12 : (1 : ℤ) ≠ 2 := by norm_num
  rcases R 0 with h0 | h0 <;> rcases R 1 with h1 | h1 <;> rcases R 2 with h2 | h2
  · exact Or.inl (aff_ext a b A B D M h01 h0 h1)
  · exact Or.inl (aff_ext a b A B D M h01 h0 h1)
  · exact Or.inl (aff_ext a b A B D M h02 h0 h2)
  · exact Or.inr (aff_ext A B a b D M h12 h1 h2)
  · exact Or.inl (aff_ext a b A B D M h12 h1 h2)
  · exact Or.inr (aff_ext A B a b D M h02 h0 h2)
  · exact Or.inr (aff_ext A B a b D M h01 h0 h1)
  · exact Or.inr (aff_ext A B a b D M h01 h0 h1)

theorem decide_bit (c : Bool) (u : ℤ) : decide ((2 * u + (c.toNat : ℤ)) % 2 = 1) = c := by
  cases c
  · exact decide_eq_false (by simp only [Bool.toNat_false, Nat.cast_zero]; omega)
  · exact decide_eq_true (by simp only [Bool.toNat_true, Nat.cast_one]; omega)

/-- On the parity class `x = 2u + c`, the condition "merged after `k+1` steps from state `s`" is
the condition "merged after `k` steps from state `step s c`" at a point `g u + h` depending
affinely on `u`, with odd slope. -/
theorem step_affine (s : State) (c : Bool) :
    ∃ g h : ℤ, g % 2 = 1 ∧ ∀ (k : ℕ) (u : ℤ),
      Phi s (k + 1) (2 * u + (c.toNat : ℤ)) ↔ Phi (step s c) k (g * u + h) := by
  -- `T x` is affine in `u`
  obtain ⟨a, b, ha, hab⟩ : ∃ a b : ℤ, a % 2 = 1 ∧
      ∀ u : ℤ, T (2 * u + (c.toNat : ℤ)) = a * u + b := by
    refine ⟨if (c.toNat : ℤ) % 2 = 0 then 1 else 3, T (c.toNat : ℤ), ?_, fun u => ?_⟩
    · split_ifs <;> norm_num
    · rw [show 2 * u + (c.toNat : ℤ) = (c.toNat : ℤ) + 2 * u by ring, T_add_two_mul]
      ring
  -- `T q` is affine in `u`
  obtain ⟨A, B, hA, hAB⟩ : ∃ A B : ℤ, A % 2 = 1 ∧
      ∀ u : ℤ, T (3 ^ s.d * (2 * u + (c.toNat : ℤ)) + s.mu) = A * u + B := by
    refine ⟨(if (3 ^ s.d * (c.toNat : ℤ) + s.mu) % 2 = 0 then 1 else 3) * 3 ^ s.d,
      T (3 ^ s.d * (c.toNat : ℤ) + s.mu), ?_, fun u => ?_⟩
    · have h3 := three_pow_emod_two s.d
      split_ifs <;> omega
    · rw [show 3 ^ s.d * (2 * u + (c.toNat : ℤ)) + s.mu
          = (3 ^ s.d * (c.toNat : ℤ) + s.mu) + 2 * (3 ^ s.d * u) by ring, T_add_two_mul]
      ring
  -- the orientation of `step_rel` is the same at every `u`
  have R : ∀ u : ℤ, A * u + B = 3 ^ (step s c).d * (a * u + b) + (step s c).mu ∨
      a * u + b = 3 ^ (step s c).d * (A * u + B) + (step s c).mu := by
    intro u
    have h := step_rel s (2 * u + (c.toNat : ℤ))
      (3 ^ s.d * (2 * u + (c.toNat : ℤ)) + s.mu) rfl
    rw [decide_bit, hab, hAB] at h
    exact h
  rcases affine_dichotomy a b A B _ _ R with H | H
  · refine ⟨a, b, ha, fun k u => ?_⟩
    unfold Phi
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hab, hAB, H u]
  · refine ⟨A, B, hA, fun k u => ?_⟩
    unfold Phi
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hab, hAB, H u]
    exact eq_comm

/-! ### Counting -/

theorem good_succ_iff (s : State) (c : Bool) (g h : ℤ) (hg : g % 2 = 1) (k : ℕ)
    (H : ∀ u : ℤ, Phi s (k + 1) (2 * u + (c.toNat : ℤ)) ↔ Phi (step s c) k (g * u + h))
    (p' : ℕ) :
    Good s (k + 1) ((2 * p' + c.toNat : ℕ) : ℤ) ↔ Good (step s c) k (sig k g h p') := by
  rw [sig_cast, good_emod]
  have key : ∀ t : ℤ, Phi s (k + 1) (((2 * p' + c.toNat : ℕ) : ℤ) + 2 ^ (k + 1) * t) ↔
      Phi (step s c) k (g * (p' : ℤ) + h + 2 ^ k * (g * t)) := by
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
    apply good_of_thin _ _ _ g (by omega)
    intro t
    exact (key t).mp (G t)
  · intro G t
    exact (key t).mpr (G (g * t))

/-- The residues of parity `c` in `merged s (k+1)` are in bijection with `merged (step s c) k`. -/
theorem card_parity (s : State) (k : ℕ) (c : Bool) :
    ((merged s (k + 1)).filter (fun p => p % 2 = c.toNat)).card
      = (merged (step s c) k).card := by
  obtain ⟨g, h, hg, H⟩ := step_affine s c
  have hc : c.toNat ≤ 1 := Bool.toNat_le c
  apply Finset.card_bij (fun p _ => sig k g h (p / 2))
  · intro p hp
    rw [Finset.mem_filter, mem_merged] at hp
    obtain ⟨⟨_, hG⟩, hpar⟩ := hp
    rw [mem_merged]
    refine ⟨sig_lt k g h _, ?_⟩
    have e : 2 * (p / 2) + c.toNat = p := by omega
    have hG' : Good s (k + 1) ((2 * (p / 2) + c.toNat : ℕ) : ℤ) := by
      rw [e]
      exact hG
    exact (good_succ_iff s c g h hg k (H k) (p / 2)).mp hG'
  · intro p₁ hp₁ p₂ hp₂ heq
    rw [Finset.mem_filter, mem_merged] at hp₁ hp₂
    have hlt₁ := hp₁.1.1
    have hlt₂ := hp₂.1.1
    rw [pow_succ] at hlt₁ hlt₂
    have h1 : p₁ / 2 < 2 ^ k := by omega
    have h2 : p₂ / 2 < 2 ^ k := by omega
    have h3 := sig_inj k g h hg h1 h2 heq
    omega
  · intro b hb
    rw [mem_merged] at hb
    obtain ⟨a, ha, rfl⟩ := sig_surj k g h hg b hb.1
    refine ⟨2 * a + c.toNat, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_merged]
      refine ⟨⟨by rw [pow_succ]; omega, ?_⟩, by omega⟩
      exact (good_succ_iff s c g h hg k (H k) a).mpr hb.2
    · have e : (2 * a + c.toNat) / 2 = a := by omega
      show sig k g h ((2 * a + c.toNat) / 2) = sig k g h a
      rw [e]

/-! ### Headline statements -/

theorem card_merged_zero (s : State) : (merged s 0).card = if s = absorbed then 1 else 0 := by
  split_ifs with hs
  · subst hs
    have hm : merged absorbed 0 = {0} := by
      ext p
      rw [mem_merged, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, _⟩
        simpa using hp
      · rintro rfl
        refine ⟨by norm_num, fun t => ?_⟩
        simp [Phi, absorbed]
    rw [hm]
    rfl
  · have hm : merged s 0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rw [mem_merged] at hp
      obtain ⟨hp0, hG⟩ := hp
      have hp0' : p = 0 := by simpa using hp0
      subst hp0'
      obtain ⟨d, μ⟩ := s
      have h0 : ((0 : ℕ) : ℤ) + 2 ^ 0 * 0 = 3 ^ d * (((0 : ℕ) : ℤ) + 2 ^ 0 * 0) + μ := hG 0
      have h1 : ((0 : ℕ) : ℤ) + 2 ^ 0 * 1 = 3 ^ d * (((0 : ℕ) : ℤ) + 2 ^ 0 * 1) + μ := hG 1
      rw [Nat.cast_zero, pow_zero, mul_zero, add_zero, mul_zero, zero_add] at h0
      rw [Nat.cast_zero, pow_zero, mul_one, zero_add, mul_one] at h1
      have hμ : μ = 0 := h0.symm
      have hd : d = 0 := by
        rcases Nat.eq_zero_or_pos d with hd | hd
        · exact hd
        · exfalso
          obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          have hpos : (0 : ℤ) < 3 ^ d' := by positivity
          rw [pow_succ] at h1
          omega
      exact hs (by rw [hμ, hd]; rfl)
    rw [hm]
    rfl

theorem card_merged_succ (s : State) (k : ℕ) :
    (merged s (k + 1)).card
      = (merged (step s false) k).card + (merged (step s true) k).card := by
  rw [← card_parity s k false, ← card_parity s k true]
  have hsplit : merged s (k + 1)
      = (merged s (k + 1)).filter (fun p => p % 2 = false.toNat)
        ∪ (merged s (k + 1)).filter (fun p => p % 2 = true.toNat) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Bool.toNat_false, Bool.toNat_true]
    constructor
    · intro hp
      rcases Nat.mod_two_eq_zero_or_one p with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint ((merged s (k + 1)).filter (fun p => p % 2 = false.toNat))
      ((merged s (k + 1)).filter (fun p => p % 2 = true.toNat)) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    simp only [Bool.toNat_false, Bool.toNat_true] at h1 h2
    omega
  conv_lhs => rw [hsplit]
  exact Finset.card_union_of_disjoint hdisj

end Coalescence

#print axioms Coalescence.card_merged_zero
#print axioms Coalescence.card_merged_succ
