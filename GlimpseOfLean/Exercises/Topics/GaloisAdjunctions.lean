import GlimpseOfLean.Library.Basic

open PiNotation

/- # Abstract non-sense 101: Galois adjunctions

In this file we will play with the simplest examples of adjunctions: Galois connections
between complete lattices. There is a lot about this topic in mathlib, but here we will
roll our own version for practice. This file builds the fundamental theory of these objects
and each lemma you prove there is named and can be reused to prove the next lemmas.
-/

namespace Tutorial

section InfSup
variable [PartialOrder X]

/-
In this section, `X` is a type equipped with a partial order relation. So you have access
to lemmas:
* `le_rfl {a : X} : a ≤ a`
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`

Curly braces around arguments mean these arguments are implicit, Lean will infer
those arguments from context.
-/

/-- An element `x₀` is an infimum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it below `x₀`.  -/
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by {
  unfold isInf at *
  rw [h]
}

/-- A set has at most one infimum. -/
def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by {
  apply le_antisymm
  {
    rw [← hx₁ ]
    apply isInf.lowerBound
    tauto
  }
  {
    rw [← hx₀ ]
    apply isInf.lowerBound
    tauto
  }
}

/-- An element `x₀` is an supremum of a set `s` in `X` if every element
of `X` is a lower bound of `s` if and only if it below `x₀`.  -/
def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x

/-
The next lemma is proven by applying `isInf.lowerBound` to `X` equipped with
the opposite order relation. You don't need to understand precisely how this is
achieved since all proofs using this trick will be offered.
-/

lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h

/-- A set has at most one supremum. -/
lemma isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁

/-- A function from `Set X` to `X` is an infimum function if it sends every set
to an infimum of this set. -/
def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)

/-- A function from `Set X` to `X` is an supremum function if it sends every set
to an supremum of this set. -/
def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)

/- The next lemma is the first crucial result if this file. If `X` admits an
infimum function then it automatically admits a supremum function. -/

lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by {
  unfold isSupFun at *
  intro s
  unfold isInfFun at *
  simp
  unfold isInf at *
  unfold isSup at *
  intro x
  constructor
  {
    intro hx
    apply isInf.lowerBound (h _)
    assumption
    -- have h1: I (upperBounds s) ∈ lowerBounds (upperBounds s) := by {
    --   rw [h]
    -- }
    -- unfold lowerBounds at h1
    -- simp at h1
    -- apply h1
    -- tauto
  }
  {
    intro hx
    unfold upperBounds
    simp
    intro a ha
    calc a
      _ <= I (upperBounds s) := by {
        rw [← h]
        unfold upperBounds
        unfold lowerBounds
        simp
        intro b hb
        apply hb
        tauto
/-         exact fun ⦃a_1⦄ a_2 ↦ a_2 ha -/
      }
      _ <= _ := by tauto
  }
}

/- Of course we also have the dual result constructing an infimum function from
a supremum one. -/

lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h

/- We are now ready for the first main definition of this file: complete lattices. -/

/-- A complete lattice is a type equipped with a partial order, an infimum function and
a supremum function. For instance `X = Set Y` equipped with the inclusion order,
the intersection function and the union function is a complete lattice. -/
class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S

/-- Turning a complete lattice `X` into the dual one. Lean will automatically pickup this
construction when using the `OrderDual` trick as above. -/
instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)

/- We can now use the first main result above to build a complete lattice from
either an infimum or a supremum function on a partially ordered type. -/

/-- Building a complete lattice structure from an infimum function on a partially ordered type. -/
def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h

/-- Building a complete lattice structure from an supremum function on a partially ordered type. -/
def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h

/- Until the end of this section, `X` will be a complete lattice. -/
variable [CompleteLattice X]

/-- The infimum function on a complete lattice. -/
notation "Inf" => CompleteLattice.I

/-- The supremum function on a complete lattice. -/
notation "Sup" => CompleteLattice.S

/- We now restate a couple of lemmas proven above in terms of complete lattices. -/

lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound

/- We now prove a series of lemmas asserting that `Inf` (and then `Sup` by duality)
behave according to your intuition. You should feel free to skip those and jump to
the adjunction section if you think you would be able to prove them and you want to
see more interesting things.

In the first lemma below, you will probably want to use
`lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s`
or reprove it as part of your proof.
-/

lemma Inf_subset {s t : Set X} (h : s ⊆ t): Inf t ≤ Inf s := by {
  -- have ht: isInf t (Inf t) := by {
  --   apply CompleteLattice.I_isInf
  -- }
  have hs: isInf s (Inf s) := by {
    apply CompleteLattice.I_isInf
  }
  unfold isInf at *
  rw [← hs]
  apply lowerBounds_mono_set at h
  apply h
  exact lowerBound_Inf t
}

lemma Sup_subset {s t : Set X} (h : s ⊆ t): Sup s ≤ Sup t :=
  Inf_subset (X := OrderDual X) h

lemma Inf_pair {x x' : X} : x ≤ x' ↔ Inf {x, x'} = x := by {
  let s: Set X := {x, x'}
  have hs: isInf s (Inf s) := by {
    apply CompleteLattice.I_isInf
  }
  unfold isInf at *
  constructor
  {
    intro h
    apply le_antisymm
    {
      apply lowerBound_Inf
      simp
    }
    {
      rw [← hs]
      simp [s]
      assumption
    }
  }
  {
    intro h
    rw [← h]
    apply lowerBound_Inf
    simp
  }
}

lemma Sup_pair {x x' : X} : x ≤ x' ↔ Sup {x, x'} = x' := by {
  rw [Set.pair_comm x x']
  exact Inf_pair (X := OrderDual X)
}

lemma Inf_self_le (x : X) : Inf {x' | x ≤ x'} = x := by {
  let s: Set X := {x' | x <= x'}
  have hs: isInf s (Inf s) := by {
    apply CompleteLattice.I_isInf
  }
  unfold isInf at *
  apply le_antisymm
  {
    apply lowerBound_Inf
    simp
  }
  {
    rw [← hs]
    simp [s]
    unfold lowerBounds
    simp
  }
}

lemma Sup_le_self (x : X) : Sup {x' | x' ≤ x} = x :=
  Inf_self_le (X := OrderDual X) x

/- Let us prove that `Set` forms a complete lattice. -/

lemma isInfInter {Y : Type} (S : Set (Set Y)) : isInf S (⋂₀ S) := by {
  unfold isInf
  intro s
  constructor
  {
    intro h
    apply Set.subset_sInter
    exact h
  }
  {
    intro h
    apply Set.subset_sInter_iff.1 at h
    exact h
  }
}

lemma isSupUnion {Y : Type} (S : Set (Set Y)) : isSup S (⋃₀ S) := by {
  unfold isSup
  intro s
  constructor
  {
    intro h
    apply Set.sUnion_subset
    exact h
  }
  {
    intro h
    apply Set.sUnion_subset_iff.1 at h
    exact h
  }
}

instance {Y : Type} : CompleteLattice (Set Y) where
  I := Set.sInter
  I_isInf := fun S ↦ isInfInter S
  S := Set.sUnion
  S_isSup := fun S ↦ isSupUnion S

end InfSup

section Adjunction
/- We are now ready for the second central definition of this file: adjunctions between
ordered types. -/

/-- A pair of functions `l` and `r` between ordered types are adjoint if
`∀ x y, l x ≤ y ↔ x ≤ r y`. One also say they form a Galois connection.
Here `l` stands for "left" and `r` stands for "right". -/
def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y

/- The example you need to keep in mind is the adjunction between direct image
and inverse image. Given `f : α → β`, we have:
* `Set.image f : Set α → Set β` with notation `f ''`
* `Set.preimage f : Set β → Set α` with notation `f ⁻¹'`
 -/

lemma image_preimage_adjunction {α β : Type} (f : α → β) :
    adjunction (Set.image f) (Set.preimage f) := by {
  intros s t
  exact Set.image_subset_iff
}

lemma adjunction.dual [PartialOrder X] [PartialOrder Y] {l : X → Y} {r : Y → X}
    (h : adjunction l r) :
    adjunction (X := OrderDual Y) (Y := OrderDual X) r l := by {
  unfold adjunction at *
  intro x y
  symm
  apply h
}

/- In this remaining of the section, `X` and `Y` are complete lattices. -/
variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]

/- We now come to the second main theorem of this file: the adjoint functor theorem for
complete lattices. This theorem says that a function between complete lattices is
a left adjoint (resp. right adjoint) if and only if it commutes with `Sup` (resp. with `Inf`).

We first define the candidate right adjoint (without making any assumption on the original
map).
  -/

/-- Constructs a candidate right adjoint for a map between complete lattices.
This is an actual adjoint if the map commutes with `Sup`, see `adjunction_of_Sup`. -/
def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}

/- The proof of the theorem below isn't long but it isn't completely obvious either.
First you need to understand the notations in the statement. `l '' s` is the direct image
of `s` under `l`. This `''` is notation for `Set.image`. Putting your cursor on this
notation and using the contextual menu to "jump to definition" will bring you to the file
defining `Set.image` and containing lots of lemmas about it. The ones that are used in
the reference solutions are

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

Proof hint: one direction is easy and doesn't use the crucial assumption. For
the other direction, you should probably first prove that `Monotone l`, ie
`∀ ⦃a b⦄, a ≤ b → l a ≤ l b`.
-/

theorem adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by {
  unfold adjunction
  unfold mk_right
  intro x y
  have hm: forall a b, a <= b -> l a <= l b := by {
    intro a b hab
    calc
      _ <= Sup {l a , l b} := by {
        apply upperBound_Sup
        simp
      }
      _ = l (Sup {a , b}) := by {
        rw [h]
        congr
        exact Eq.symm (Set.image_pair l a b)
      }
      _ <= _             := by {
        rw [Sup_pair.1 hab]
      }
  }
  constructor
  {
    intro h'
    calc
      _ <= Sup {x} := by {
        apply upperBound_Sup
        simp
      }
      _ <= _       := by {
        apply Sup_subset
        simp
        assumption
      }
  }
  {
    intro h'
    let s := {x | l x ≤ y}
    calc
      _ <= l (Sup s) := by {
        apply hm
        assumption
      }
      _ = Sup (l '' s) := by {
        apply h
      }
      _ <= Sup {y' | y' <= y} := by {
        simp [s]
        apply Sup_subset
        simp
      }
      _ = _ := by {
        apply Sup_le_self
      }
  }
}

/- Of course we can play the same game to construct left adjoints. -/

/-- Constructs a candidate left adjoint for a map between complete lattices.
This is an actual adjoint if the map commutes with `Inf`, see `adjunction_of_Inf`. -/
def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology
/- In this section we apply the theory developed above to point-set topology.
Our first goal is to endow the type `Topology X` of topologies on a given type
with a complete lattice structure. We then turn any map `f : X → Y` into an
adjunction `(f⁎, f ^*)` between `Topology X` and `Topology Y` and use it
to build the product topology. Of course mathlib knows all this, but we'll
continue to build our own theory.
-/

@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_iUnion : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_iInter : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)

/- Let's run two quick sanity checks on our definition since so many textbooks include redundant
conditions it the definition of topological spaces. -/

lemma isOpen_empty (T : Topology X) : T.isOpen ∅ := by {
  have : (∅ : Set X) = ⋃ i : Empty, i.rec := by
    rw [Set.iUnion_of_empty]
  rw [this]
  exact T.isOpen_iUnion Empty.rec
}

lemma isOpen_univ (T : Topology X) : T.isOpen Set.univ := by {
  have : (Set.univ : Set X) = ⋂ i : Empty, i.rec := by
    rw [Set.iInter_of_empty]
  rw [this]
  exact T.isOpen_iInter  Empty.rec (Finite.of_fintype Empty)
}

/- The `ext` attribute on the definition of `Topology` tells Lean to automatically build the following
extensionality lemma:
`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen`
and it also registers this lemma for use by the `ext` tactic (we will come back to this below).
-/

/-- We order `Topology X` using the order dual to the order induced by
`Set (Set X)`. There are good reasons for this choice but they are beyond the scope of this
tutorial. -/
instance : PartialOrder (Topology X) :=
PartialOrder.lift (β := OrderDual $ Set (Set X)) Topology.isOpen (fun _ _ ↦ (Topology.ext_iff).2)

/-- The supremum function on `Topology X`. -/
def SupTop (s : Set (Topology X)) : Topology X where
  isOpen := fun V ↦ ∀ T ∈ s, T.isOpen V
  isOpen_iUnion := by {
    intros ι t ht a ha
    exact a.isOpen_iUnion fun i ↦ ht i a ha
  }
  isOpen_iInter := by {
    intros ι t ht hι a ha
    exact a.isOpen_iInter (fun i ↦ ht i a ha) hι
}

/-
Because the supremum function above comes from the supremum function of `OrderDual (Set (Set X))`,
it is indeed a supremum function. We could state an abstract lemma saying that, but here a direct
proof is just as easy and a lot of fun.
-/
lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩

/- We can use our abstract theory to get an infimum function for free, hence a complete lattice
structure on `Topology X`.
Note that our abstract theory is indeed doing non-trivial work: the infimum function does *not*
come from `OrderDual (Set (Set X))`.
-/

instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop

/- Let us restate in complete lattice notation what our construction of `Sup` was. The proof
is simply saying "this is true by definition". -/

lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl

/- We now start building our adjunction between `Topology X` and `Topology Y` induced by any
map `f : X → Y`. We will build the left adjoint by hand and then invoke our adjoint functor
theorem.
-/

def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_iUnion := by {
    intro i s h
    simp at h
    rw [@Set.preimage_iUnion]
    apply T.isOpen_iUnion h
  }
  isOpen_iInter := by {
    intro i s h hf
    rw [@Set.preimage_iInter]
    apply T.isOpen_iInter h hf
}

postfix:1024 "⁎" => push -- type using `\_*`

/-- A map `f : X → Y` is continuous with respect to topologies `T` and `T'` if the preimage of
every open set is open.-/
def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'

/- Let us check the definition is indeed saying what we claimed it says. -/
example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl

/- Note how the following proof uses the `ext` tactic which knows that two topologies are
equal iff they have the same open sets thanks to the `ext` attribute on the definition
of `Topology`. -/

lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by {
  ext V
  exact Iff.rfl
}

/- We want a right adjoint for `f ⁎` so we need to check it commutes with `Sup`.
You may want to use
`Set.ball_image_iff : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x)`
where "ball" stands for "bounded for all", ie `∀ x ∈ ...`.
-/

lemma push_Sup (f : X → Y) {t : Set (Topology X)} : f ⁎ (Sup t) = Sup (f ⁎ '' t) := by {
  ext Ys
  unfold push
  simp
  rw [isOpen_Sup, isOpen_Sup]
  simp
}

def pull (f : X → Y) (T : Topology Y) : Topology X := mk_right (push f) T

postfix:1024 "^*" => pull

def ProductTopology {ι : Type} {X : ι → Type} (T : Π i, Topology (X i)) : Topology (Π i, X i) :=
Inf (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i)))

lemma Continuous_iff (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl

lemma ContinuousProductTopIff {ι : Type} {X : ι → Type} (T : Π i, Topology (X i))
  {Z : Type} (TZ : Topology Z) {f : Z → Π i, X i}:
    Continuous TZ (ProductTopology T) f ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i) := by {
  -- calc
  --   Continuous TZ (ProductTopology T) f
  --   _ ↔ f ⁎ TZ ∈ lowerBounds (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i))) := by {
  --         rw [CompleteLattice.I_isInf]
  --         exact Iff.rfl
  --         }
  --   _ ↔ ∀ i, f ⁎ TZ ≤ (fun x ↦ x i) ^* (T i)        := by rw [lowerBounds_range]
  --   _ ↔ ∀ i, (fun x ↦ x i) ⁎ (f ⁎ TZ) ≤ T i        := by {
  --         apply forall_congr'
  --         intro i
  --         -- rw [pull, ← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
  --         rw [pull, ← adjunction_of_Sup (fun s ↦ push_Sup _)]
  --         }
  --   _ ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i)  := Iff.rfl

  -- unfold Continuous ProductTopology
  -- rw [← CompleteLattice.I_isInf, lowerBounds_range]
  -- apply forall_congr'
  -- intro i
  -- unfold pull
  -- -- rw [← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
  -- rw [← adjunction_of_Sup (fun s ↦ push_Sup _)]
  -- rfl

  -- rw [Continuous_iff]
  -- have heq : forall i (Xis : Set (X i)), (fun z ↦ f z i) ⁻¹' Xis = f ⁻¹' {x : (Π (i : ι), X i) | x i ∈ Xis} := by {
  --   intro Xis i
  --   ext z
  --   simp
  -- }
  constructor
  {
    unfold ProductTopology
    intro h i
    rw [Continuous_iff]
    intro Xis hXis
    rw [Continuous_iff] at h
    have heq : (fun z ↦ f z i) ⁻¹' Xis = f ⁻¹' {x : (Π (i : ι), X i) | x i ∈ Xis} := by {
      ext z
      simp
    }
    rw [heq]
    apply h
    let Ts : Set (Topology (Π (i : ι), X i)) := Set.range fun i ↦ (fun x ↦ x i)^* (T i)
    unfold pull at *
    have hle: Inf Ts <= (fun x ↦ x i)^* (T i) := by {
      apply lowerBound_Inf
      exact Set.mem_range_self i
    }
    unfold pull at *
    apply hle
    unfold mk_right at *
    apply isOpen_Sup.2
    intro PT hPT
    simp at *
    apply hPT at hXis
    simp at *
    unfold push at hXis
    simp at hXis
    have h_not_necessary: (fun (x : Π i, X i) ↦ x i) ⁻¹' Xis = {x | x i ∈ Xis} := by {
      rfl
    }
    -- -- rw [h_not_necessary] at hXis
    -- rw [← h_not_necessary]
    exact hXis
  }
  {
    -- intro h
    -- unfold ProductTopology
    -- unfold Continuous
    -- rw [← CompleteLattice.I_isInf]
    -- rw [lowerBounds_range]
    -- intro i
    -- unfold pull
    -- rw [← adjunction_of_Sup (by {
    --   apply push_Sup
    -- })]
    -- unfold Continuous at h
    -- apply h

    intro h
    unfold ProductTopology
    rw [Continuous_iff]
    intro tuples h_tuples
    -- rw [Continuous_iff] at h
    have h2: forall i V, (T i).isOpen V -> TZ.isOpen ((fun z ↦ f z i) ⁻¹' V) := by {
      exact h
    }
    have h3: forall i, (fun x ↦ x i)⁎ (f⁎ TZ) ≤ T i := by {
      -- exact h
      exact h2
    }
    -- rw [push_push] at h_key
    -- rw [adjunction_of_Sup] at h_key
    have h4_key: forall i, (f⁎ TZ) <= mk_right (fun x ↦ x i)⁎ (T i) := by {
      intro i
      -- This is fundamentally how you prove `TZ.isOpen (f ⁻¹' tuples)`.
      rw [<- adjunction_of_Sup (by {
        apply push_Sup
      })]
      apply h3
    }
    have h5: (f⁎ TZ) <= Inf (Set.range fun i ↦ mk_right (fun x ↦ x i)⁎ (T i)) := by {
      rw [← CompleteLattice.I_isInf]
      rw [lowerBounds_range]
      exact h4_key
    }
    apply h5  -- This is how you prove `TZ.isOpen (f ⁻¹' tuples)`.
    exact h_tuples

  --   unfold Continuous at h

  --   have heq: f ⁻¹' tuples = ⋂ i, (fun z ↦ f z i) ⁻¹' (tuples i) := by {
  --   }
  --   let Ts : Set (Topology (Π (i : ι), X i)) := Set.range fun i ↦ (fun x ↦ x i)^* (T i)

  --   }
  --   apply h'
  --   rw [isOpen_Sup]
  --   have hle2: mk_right (fun x ↦ x i)⁎ (T i) <=
  --   unfold Membership.mem
  --   simp

  --   simp

  --   unfold mk_of_Sup


  --   unfold push

  --   apply hXis
  --   simp
  --   rw [isOpen_Sup] at h

  --   simp at *
  --   simp
  --   unfold Continuous

  --   simp
  }
}

end Topology

namespace Subgroups

@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ ⦃x y : G⦄, x ∈ carrier → y ∈ carrier → x*y ∈ carrier
  inv_mem : ∀ ⦃x : G⦄, x ∈ carrier → x⁻¹ ∈ carrier

instance [Group G] : Membership G (Subgroup G) := ⟨fun x H ↦ x ∈ H.carrier⟩

variable {G : Type} [Group G]

instance : PartialOrder (Subgroup G) :=
  PartialOrder.lift Subgroup.carrier (fun _ _ ↦ (Subgroup.ext_iff).2)

/- An intersection of subgroups is a subgroup. -/

def SubgroupInf (s : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ H ∈ s, H.carrier
  one_mem := by {
    rw [Set.mem_iInter₂]
    -- apply Set.mem_iInter₂_of_mem
    intro i hi
    apply Subgroup.one_mem
  }
  mul_mem := by {
    intro x y hx hy
    rw [Set.mem_iInter₂]
    -- apply Set.mem_iInter₂_of_mem
    intro i hi
    apply Subgroup.mul_mem
    {
      rw [Set.mem_iInter₂] at hx
      apply hx
      apply hi
    }
    {
      rw [Set.mem_iInter₂] at hy
      apply hy
      apply hi
    }
  }
  inv_mem := by {
    intro x hx
    rw [Set.mem_iInter₂]
    intro i hi
    apply Subgroup.inv_mem
    rw [Set.mem_iInter₂] at hx
    apply hx
    apply hi
  }

lemma SubgroupInf_carrier (s : Set (Subgroup G)) :
  (SubgroupInf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
by simp [SubgroupInf]

lemma SubgroupInf_is_Inf : isInfFun (SubgroupInf : Set (Subgroup G) → Subgroup G) := by {
  unfold isInfFun
  intro s
  unfold isInf
  intro x
  symm
  apply Set.subset_iInter₂_iff

  -- constructor
  -- {
  --   intro h
  --   -- unfold SubgroupInf
  --   -- have goal: x.carrier ⊆ ⋂ H ∈ s, H.carrier := by {
  --   --   exact Set.subset_iInter₂ h
  --   -- }
  --   -- apply goal

  --   -- exact Set.subset_iInter₂ h
  --   apply Set.subset_iInter₂_iff.2
  --   apply h
  -- }
  -- {
  --   intro h
  --   apply Set.subset_iInter₂_iff.1
  --   apply h
  -- }
}

instance : CompleteLattice (Subgroup G) := CompleteLattice.mk_of_Inf SubgroupInf_is_Inf

lemma Inf_carrier (s : Set (Subgroup G)) : (Inf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
  SubgroupInf_carrier s

def forget (H : Subgroup G) : Set G := H.carrier

def generate : Set G → Subgroup G := mk_left forget

lemma generate_forget_adjunction : adjunction (generate : Set G → Subgroup G) forget := by {
  sorry
}

variable {G' : Type} [Group G']

def pull (f : G →* G') (H' : Subgroup G') : Subgroup G where
  carrier := f ⁻¹' H'.carrier
  one_mem := by {
    sorry
  }
  mul_mem := by {
    sorry
  }
  inv_mem := by {
    sorry
  }

lemma pull_carrier (f : G →* G') (H' : Subgroup G') : (pull f H').carrier = f ⁻¹' H'.carrier :=
  rfl

/- Let's be really lazy and define subgroup push-forward by adjunction. -/

def push (f : G →* G') : Subgroup G → Subgroup G' := mk_left (pull f)

lemma push_pull_adjunction (f : G →* G') : adjunction (push f) (pull f) := by {
  sorry
}

end Subgroups

section
/- Our next concrete target is
`push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`

which will require a couple more abstract lemmas. -/

variable {X : Type} [PartialOrder X]
         {Y : Type} [PartialOrder Y]

lemma unique_left {l l' : X → Y} {r : Y → X} (h : adjunction l r) (h' : adjunction l' r) :
    l = l' := by {
  sorry
}

lemma unique_right {l : X → Y} {r r' : Y → X} (h : adjunction l r) (h' : adjunction l r') :
    r = r' := by {
  sorry
}

variable {Z : Type} [PartialOrder Z]

lemma adjunction.compose {l : X → Y} {r : Y → X} (h : adjunction l r)
  {l' : Y → Z} {r' : Z → Y} (h' : adjunction l' r') : adjunction (l' ∘ l) (r ∘ r') := by {
  sorry
}



end

namespace Subgroups
variable {G : Type} [Group G] {G' : Type} [Group G']

/- As a last challenge, we propose the following lemma. -/

/-- The image under a group morphism of the subgroup generated by some set `S`
is generated by the image of `S`. -/
lemma push_generate (f : G →* G') : push f ∘ generate = generate ∘ (Set.image f) := by {
  sorry
}

end Subgroups
end Tutorial
