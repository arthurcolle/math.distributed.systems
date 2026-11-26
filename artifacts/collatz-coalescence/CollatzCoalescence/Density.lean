import Mathlib

namespace Coalescence

/-- If `G` is a set of residues modulo `m`, at least `G.card * (N / m)` of the `n < N` reduce into `G`. -/
theorem card_filter_mod_ge (m : ℕ) (hm : 0 < m) (G : Finset ℕ) (hG : ∀ g ∈ G, g < m) (N : ℕ) :
    G.card * (N / m) ≤ ((Finset.range N).filter (fun n => n % m ∈ G)).card := by
  have h : (G ×ˢ Finset.range (N / m)).card ≤
      ((Finset.range N).filter (fun n => n % m ∈ G)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + m * p.2)
    · rintro ⟨g, j⟩ hp
      have hp' : g ∈ G ∧ j < N / m := by simpa using hp
      obtain ⟨hg, hj⟩ := hp'
      have hgm : g < m := hG g hg
      have hlt : g + m * j < N := by
        calc g + m * j < m * (j + 1) := by rw [Nat.mul_succ]; omega
          _ ≤ m * (N / m) := Nat.mul_le_mul_left m hj
          _ ≤ N := Nat.mul_div_le N m
      have hmod : (g + m * j) % m = g := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hgm]
      have hgoal : g + m * j ∈ (Finset.range N).filter (fun n => n % m ∈ G) := by
        rw [Finset.mem_filter, Finset.mem_range, hmod]
        exact ⟨hlt, hg⟩
      exact hgoal
    · rintro ⟨g, j⟩ hp ⟨g', j'⟩ hp' heq
      have hp1 : g ∈ G ∧ j < N / m := by simpa using hp
      have hp2 : g' ∈ G ∧ j' < N / m := by simpa using hp'
      have hgm : g < m := hG g hp1.1
      have hgm' : g' < m := hG g' hp2.1
      have heq' : g + m * j = g' + m * j' := heq
      have hgg : g = g' := by
        have := congrArg (· % m) heq'
        simp only [Nat.add_mul_mod_self_left] at this
        rwa [Nat.mod_eq_of_lt hgm, Nat.mod_eq_of_lt hgm'] at this
      subst hgg
      have hjj : j = j' := by
        have : m * j = m * j' := by omega
        exact Nat.eq_of_mul_eq_mul_left hm this
      rw [hjj]
  rwa [Finset.card_product, Finset.card_range] at h

/-- A property that holds on residue classes mod `2^K` of proportion arbitrarily close to `1`
has natural density one. -/
theorem density_one_of_classes (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∃ G : Finset ℕ, (∀ g ∈ G, g < 2 ^ K) ∧
        (1 - ε) * (2 : ℝ) ^ K ≤ (G.card : ℝ) ∧ ∀ n : ℕ, n % 2 ^ K ∈ G → P n) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * (N : ℝ) ≤ (((Finset.range N).filter P).card : ℝ) := by
  intro ε hε
  obtain ⟨K, G, hG, hcard, hP⟩ := h (ε / 2) (by positivity)
  refine ⟨⌈(2 : ℝ) ^ (K + 1) / ε⌉₊, fun N hN => ?_⟩
  by_cases h1 : 1 ≤ ε
  · have hle : (1 - ε) * (N : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)
    exact hle.trans (Nat.cast_nonneg _)
  · have h1' : ε < 1 := lt_of_not_ge h1
    have hNreal : (2 : ℝ) ^ (K + 1) / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have hN2 : 2 * (2 : ℝ) ^ K ≤ ε * N := by
      rw [div_le_iff₀ hε, pow_succ] at hNreal
      linarith
    have hsub : ((Finset.range N).filter (fun n => n % 2 ^ K ∈ G)).card ≤
        ((Finset.range N).filter P).card := by
      apply Finset.card_le_card
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hP n hn.2⟩
    have hnat : G.card * (N / 2 ^ K) ≤ ((Finset.range N).filter P).card :=
      (card_filter_mod_ge (2 ^ K) (by positivity) G hG N).trans hsub
    have hreal : (G.card : ℝ) * ((N / 2 ^ K : ℕ) : ℝ) ≤
        (((Finset.range N).filter P).card : ℝ) := by
      exact_mod_cast hnat
    have hdiv : (N : ℝ) ≤ (2 : ℝ) ^ K * ((N / 2 ^ K : ℕ) : ℝ) + (2 : ℝ) ^ K := by
      have hlt : N < 2 ^ K * (N / 2 ^ K + 1) := Nat.lt_mul_div_succ N (by positivity)
      have hlt' : (N : ℝ) < ((2 ^ K * (N / 2 ^ K + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at hlt'
      linarith
    have hq0 : (0 : ℝ) ≤ ((N / 2 ^ K : ℕ) : ℝ) := Nat.cast_nonneg _
    generalize ((N / 2 ^ K : ℕ) : ℝ) = q at hreal hdiv hq0
    have hM : 0 < (2 : ℝ) ^ K := by positivity
    have hc : 0 ≤ 1 - ε / 2 := by linarith
    have hstep1 : (1 - ε) * (N : ℝ) ≤ (1 - ε / 2) * ((2 : ℝ) ^ K * q) := by
      have hprod : 0 ≤ (1 - ε / 2) * ((2 : ℝ) ^ K * q + (2 : ℝ) ^ K - N) :=
        mul_nonneg hc (by linarith)
      have hεM : 0 ≤ ε * (2 : ℝ) ^ K := by positivity
      nlinarith
    have hstep2 : (1 - ε / 2) * ((2 : ℝ) ^ K * q) ≤ (G.card : ℝ) * q := by
      have := mul_le_mul_of_nonneg_right hcard hq0
      linarith
    exact hstep1.trans (hstep2.trans hreal)

end Coalescence

#print axioms Coalescence.card_filter_mod_ge
#print axioms Coalescence.density_one_of_classes
