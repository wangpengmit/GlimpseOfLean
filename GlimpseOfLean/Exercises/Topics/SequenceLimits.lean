import GlimpseOfLean.Library.Basic

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  linarith
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  linarith
}

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|1 - 1|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  unfold seq_limit
  intro ε hε
  use 0
  intro n hn
  rw [h]
  simp
  linarith
}


/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  unfold seq_limit at h
  specialize h (l / 2) (by linarith)
  rcases h with ⟨ N , h ⟩
  use N
  intro n hn
  specialize h _ hn
  rw [abs_le] at h
  linarith
}


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  unfold seq_limit
  intro ε hε
  unfold seq_limit at hu
  unfold seq_limit at hw
  specialize hu ε hε
  rcases hu with ⟨ N₁ , hu ⟩
  specialize hw ε hε
  rcases hw with ⟨ N₂ , hw ⟩
  use max N₁ N₂
  intro n hn
  rw [abs_le]
  rw [ge_max_iff] at hn
  rcases hn with ⟨ hn1 , hn2 ⟩
  specialize hu n (by linarith)
  rw [abs_le] at hu
  specialize hw n (by linarith)
  rw [abs_le] at hw
  rcases hu with ⟨ hu1 , hu2 ⟩
  rcases hw with ⟨ hw1 , hw2 ⟩
  constructor
  . calc
      -ε ≤ u n - l := by linarith
       _ ≤ v n - l := by exact tsub_le_tsub_right (h n) l
  . calc
     v n - l ≤ w n - l := by exact tsub_le_tsub_right (h' n) l
           _ ≤ ε       := by linarith
}



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  intro h h'
  unfold seq_limit at h
  unfold seq_limit at h'
  apply eq_of_abs_sub_le_all
  intro ε hε
  specialize h (ε / 2) (by linarith)
  specialize h' (ε / 2) (by linarith)
  rcases h with ⟨ N , h ⟩
  rcases h' with ⟨ N' , h' ⟩
  set n := max N N'
  have hN : n ≥ N := by exact Nat.le_max_left N N'
  have hN' : n ≥ N' := by exact Nat.le_max_right N N'
  specialize h n hN
  specialize h' n hN'
  have hn : |l - u n| ≤ ε / 2 := by rw [abs_sub_comm]
                                    linarith
  have hn' : |u n - l'| ≤ ε / 2 := by linarith
  calc
    |l - l'| = |l - u n + (u n - l')| := by ring
           _ ≤ |l - u n| + |u n - l'| := by apply abs_add
           _ ≤ ε                      := by linarith
}



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  unfold seq_limit
  unfold is_seq_sup at h
  unfold non_decreasing at h'
  intro ε hε
  rcases h with ⟨ h1 , h2 ⟩
  specialize h2 ε (by linarith)
  rcases h2 with ⟨ n , h2 ⟩
  use n
  intro m hm
  rw [abs_le]
  -- specialize h' n m (by linarith)
  constructor
  . calc
      -ε ≤ u n - M   := by linarith
       _ ≤ u m - M   := by linarith [h' n m (by linarith)]
  . specialize h1 m
    linarith
}

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  intro h N N'
  unfold extraction at h
  use max N N'
  constructor
  {
    exact Nat.le_max_right N N'
  }
  {
    calc
      φ (max N N') ≥ max N N' := by apply id_le_extraction'
                                    exact h
                 _ ≥ N := by exact Nat.le_max_left N N'
  }
}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`
-/


/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  intro h ε hε N
  unfold cluster_point at h
  rcases h with ⟨ φ , ⟨ hφ , Hlimit ⟩ ⟩
  unfold seq_limit at Hlimit
  specialize Hlimit ε (by apply hε )
  rcases Hlimit with ⟨ N' , Hlimit ⟩
  use φ (max N N')
  constructor
  {
    calc
      φ (max N N') ≥ max N N' := by {
                                   exact id_le_extraction' hφ (N ⊔ N')
                                 }
                _ ≥ N         := by exact Nat.le_max_left N N'
/-     linarith [id_le_extraction' hφ (N ⊔ N') , Nat.le_max_left N N'] -/
  }
  {
    apply Hlimit
    exact Nat.le_max_right N N'
  }
}


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
    unfold seq_limit at *
    intro ε hε
    specialize h ε hε
    rcases h with ⟨ N , h ⟩
    use N
    intro n hn
    apply h
    linarith [id_le_extraction' hφ n]
}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  apply eq_of_abs_sub_le_all
  intro ε hε
  unfold cluster_point at *
  rcases ha with ⟨ φ , ⟨ hφ , ha ⟩ ⟩
  unfold seq_limit at *
  unfold extraction at *
  specialize ha (ε / 2) (by linarith)
  rcases ha with ⟨ N , ha ⟩
  specialize hl (ε / 2) (by linarith)
  rcases hl with ⟨ N', hl ⟩
  let n := φ (max N N')
  have h2 : |u n - l| ≤ ε / 2 := by {
    apply hl
    calc n
      _ ≥ max N N' := by exact id_le_extraction' hφ (N ⊔ N')
      _ ≥ N'       := by exact Nat.le_max_right N N'
  }
  have h1 : |a - u n| ≤ ε / 2 := by {
    rw [abs_sub_comm]
    apply ha
    exact Nat.le_max_left N N'
  }
  calc |a - l|
    _ = |a - u n + (u n - l)| := by ring
    _ ≤ |a - u n| + |u n - l| := by apply abs_add_le
/-     _ ≤ ε / 2 + ε / 2         := by linarith -/
    _ ≤ ε                     := by linarith
}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  rintro ⟨ l , hl ⟩
  unfold CauchySequence
  intro ε hε
  unfold seq_limit at *
  specialize hl (ε / 2) (by linarith)
  rcases hl with ⟨ N , hl ⟩
  use N
  intro p q hp hq
  have hlp : |u p - l| ≤ ε / 2 := by {
    apply hl
    linarith
  }
  have hlq : |l - u q| ≤ ε / 2 := by {
    rw [abs_sub_comm]
    apply hl
    linarith
  }
  calc
    _ = |u p - l + (l - u q)|  := by ring
    _ <= |u p - l| + |l - u q| := by exact abs_add_le (u p - l) (l - u q)
/-     _ <= ε / 2 + ε / 2         := by linarith -/
    _ <= _                     := by linarith
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by {
  unfold cluster_point at *
  unfold CauchySequence at *
  unfold seq_limit at *
  rcases hl with ⟨ φ , ⟨ hφ , hl ⟩ ⟩
  intro ε hε
  specialize hu (ε / 2) (by linarith)
  specialize hl (ε / 2) (by linarith)
  rcases hu with ⟨  N₁ , hu ⟩
  rcases hl with ⟨ N₂ , hl ⟩
  let N := max N₁ N₂
  use φ N
  intro n hn
  have hnN: n >= N := by {
    calc
      _ >= φ N := by linarith
      _ >= _   := by exact id_le_extraction' hφ N
  }
  have hnN1: n >= N₁ := by {
    calc
      _ >= N   := by linarith
      _ >= _   := by exact Nat.le_max_left N₁ N₂
  }
  have hnN2: n >= N₂ := by {
    calc
      _ >= N   := by linarith
      _ >= _   := by exact Nat.le_max_right N₁ N₂
  }
  have h1: |u n - u (φ n)| <= ε / 2 := by {
    apply hu
    . linarith
    . calc
        _ >= n := by exact id_le_extraction' hφ n
        _ >= _ := by linarith
  }
  have h2: |u (φ n) - l| <= ε / 2 := by {
    apply hl
    linarith
  }
  calc
    _ = |u n - u (φ n) + (u (φ n) - l)|    := by ring
    _ <= |u n - u (φ n)| + |(u (φ n) - l)| := by exact abs_add_le (u n - u (φ n)) (u (φ n) - l)
/-     _ <= ε / 2 + ε / 2                     := by linarith -/
    _ <= _                                 := by linarith
}
