---
title     : "Logic: Propositions as Type"
layout    : page
permalink : /Logic
---

This chapter describes the connection between logical connectives
(conjunction, disjunction, implication, for all, there exists,
equivalence) and datatypes (product, sum, function, dependent
function, dependent product, Martin Löf equivalence).

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
\end{code}

This chapter introduces the basic concepts of logic, including
conjunction, disjunction, true, false, implication, negation,
universal quantification, and existential quantification.
Each concept of logic is represented by a corresponding standard
data type.

+ *conjunction* is *product*
+ *disjunction* is *sum*
+ *true* is *unit type*
+ *false* is *empty type*
+ *implication* is *function space*
+ *negation* is *function to empty type*
+ *universal quantification* is *dependent function*
+ *existential quantification* is *dependent product*

We also discuss how equality is represented, and the relation
between *intuitionistic* and *classical* logic.


## Isomorphism

As a prelude, we begin by introducing the notion of isomorphism.
In set theory, two sets are isomorphism if they are in 1-to-1 correspondence.
Here is the formal definition of isomorphism.
\begin{code}
record _≃_ (A B : Set) : Set where
  field
    to : A → B
    fro : B → A
    invˡ : ∀ (x : A) → fro (to x) ≡ x
    invʳ : ∀ (y : B) → to (fro y) ≡ y
open _≃_
\end{code}
Let's unpack the definition. An isomorphism between sets `A` and `B` consists
of four things:
+ A function `to` from `A` to `B`,
+ A function `fro` from `B` back to `A`,
+ Evidence `invˡ` asserting that `to` followed by `from` is the identity,
+ Evidence `invʳ` asserting that `from` followed by `to` is the identity.
The declaration `open _≃_` makes avaialable the names `to`, `fro`,
`invˡ`, and `invʳ`, otherwise we would need to write `_≃_.to` and so on.

The above is our first example of a record declaration. It is equivalent
to a corresponding inductive data declaration.
\begin{code}
data _≃′_ : Set → Set → Set where
  mk-≃′ : ∀ {A B : Set} →
         ∀ (to : A → B) →
         ∀ (fro : B → A) → 
         ∀ (invˡ : (∀ (x : A) → fro (to x) ≡ x)) →
         ∀ (invʳ : (∀ (y : B) → to (fro y) ≡ y)) →
         A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g gfx≡x fgy≡y) = f

fro′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
fro′ (mk-≃′ f g gfx≡x fgy≡y) = g

invˡ′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → fro′ A≃B (to′ A≃B x) ≡ x)
invˡ′ (mk-≃′ f g gfx≡x fgy≡y) = gfx≡x

invʳ′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (fro′ A≃B y) ≡ y)
invʳ′ (mk-≃′ f g gfx≡x fgy≡y) = fgy≡y
\end{code}
We construct values of the record type with the syntax:

    record
      { to = f
      ; fro = g
      ; invˡ = gfx≡x
      ; invʳ = fgy≡y
      }

which corresponds to using the constructor of the corresponding
inductive type:

    mk-≃′ f g gfx≡x fgy≡y

where `f`, `g`, `gfx≡x`, and `fgy≡y` are values of suitable types.
      
Isomorphism is an equivalence, meaning that it is reflexive, symmetric,
and transitive.  To show isomorphism is reflexive, we take both `to`
and `fro` to be the identity function.
\begin{code}
≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to = λ x → x
    ; fro = λ y → y
    ; invˡ = λ x → refl
    ; invʳ = λ y → refl
    } 
\end{code}
To show isomorphism is symmetric, we simply swap the roles of `to`
and `fro`, and `invˡ` and `invʳ`.
\begin{code}
≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { to = fro A≃B
    ; fro = to A≃B
    ; invˡ = invʳ A≃B
    ; invʳ = invˡ A≃B
    }
\end{code}
To show isomorphism is transitive, we compose the `to` and `fro` functions, and use
equational reasoning to combine the inverses.
\begin{code}
≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to = λ x → to B≃C (to A≃B x)
    ; fro = λ y → fro A≃B (fro B≃C y)
    ; invˡ = λ x →
        begin
          fro A≃B (fro B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (fro A≃B) (invˡ B≃C (to A≃B x)) ⟩
          fro A≃B (to A≃B x)
        ≡⟨ invˡ A≃B x ⟩
          x
        ∎ 
    ; invʳ = λ y →
        begin
          to B≃C (to A≃B (fro A≃B (fro B≃C y)))
        ≡⟨ cong (to B≃C) (invʳ A≃B (fro B≃C y)) ⟩
          to B≃C (fro B≃C y)
        ≡⟨ invʳ B≃C y ⟩
          y
        ∎
     }
\end{code}

We will make good use of isomorphisms in what follows to demonstrate
that operations on types such as product and sum satisfy properties
akin to associativity, commutativity, and distributivity.

## Embedding

We will also need the notion of *embedding*, which is a weakening
of isomorphism.  While an isomorphism shows that two types are
in one-to-one correspondence, and embedding shows that the first
type is, in a sense, included in the second; or, equivalently,
that there is a many-to-one correspondence between the second
type and the first.

Here is the formal definition of embedding.
\begin{code}
record _≲_ (A B : Set) : Set where
  field
    to : A → B
    fro : B → A
    invˡ : ∀ (x : A) → fro (to x) ≡ x
open _≲_
\end{code}
It is the same as an isomorphism, save that it lacks the `invʳ` field.
Hence, we know that `fro` is left inverse to `to`, but not that it is
a right inverse.

Embedding is reflexive and transitive.  The proofs are cut down
versions of the similar proofs for isomorphism, simply dropping the
right inverses.
\begin{code}
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to = λ x → x
    ; fro = λ y → y
    ; invˡ = λ x → refl
    } 

≲-tran : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-tran A≲B B≲C =
  record
    { to = λ x → to B≲C (to A≲B x)
    ; fro = λ y → fro A≲B (fro B≲C y)
    ; invˡ = λ x →
        begin
          fro A≲B (fro B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (fro A≲B) (invˡ B≲C (to A≲B x)) ⟩
          fro A≲B (to A≲B x)
        ≡⟨ invˡ A≲B x ⟩
          x
        ∎ 
     }
\end{code}
It is also easy to see that if two types embed in each other,
and the embedding functions correspond, then they are isomorphic.
This is a weak form of anti-symmetry.
\begin{code}
≲-antisym : ∀ {A B : Set} → (A≲B : A ≲ B) → (B≲A : B ≲ A) →
  (to A≲B ≡ fro B≲A) → (fro A≲B ≡ to B≲A) → A ≃ B
≲-antisym A≲B B≲A to≡fro fro≡to =
  record
    { to   = to A≲B
    ; fro  = fro A≲B
    ; invˡ = invˡ A≲B
    ; invʳ = λ y →
        begin
          to A≲B (fro A≲B y)
        ≡⟨ cong (\w → to A≲B (w y)) fro≡to ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong (\w → w (to B≲A y)) to≡fro ⟩
          fro B≲A (to B≲A y)
        ≡⟨ invˡ B≲A y ⟩
          y
        ∎
    }
\end{code}
The first three components are copied from the embedding, while the
last combines the left inverse of `B ≲ A` with the equivalences of
the `to` and `fro` components from the two embeddings to obtain
the right inverse of the isomorphism.


## Conjunction is product

Given two propositions `A` and `B`, the conjunction `A × B` holds
if both `A` holds and `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _×_ : Set → Set → Set where
  _,_ : ∀ {A B : Set} → A → B → A × B
\end{code}
Evidence that `A × B` holds is of the form
`(M , N)`, where `M` is evidence that `A` holds and
`N` is evidence that `B` holds.

Given evidence that `A × B` holds, we can conclude that either
`A` holds or `B` holds.
\begin{code}
fst : ∀ {A B : Set} → A × B → A
fst (x , y) = x

snd : ∀ {A B : Set} → A × B → B
snd (x , y) = y
\end{code}
If `L` is evidence that `A × B` holds, then `fst L` is evidence
that `A` holds, and `snd L` is evidence that `B` holds.

Equivalently, we could also declare product as a record type.
\begin{code}
record _×′_ (A B : Set) : Set where
  field
    fst′ : A
    snd′ : B
open _×′_
\end{code}
We construct values of the record type with the syntax:

    record
      { fst′ = M
      ; snd′ = N
      }

which corresponds to using the constructor of the corresponding
inductive type:

    ( M , N )

where `M` is a term of type `A` and `N` is a term of type `B`.

We set the precedence of conjunction so that it binds less
tightly than anything save disjunction, and of the pairing
operator so that it binds less tightly than any arithmetic
operator.
\begin{code}
infixr 2 _×_
infixr 4 _,_
\end{code}
Thus, `m ≤ n × n ≤ p` parses as `(m ≤ n) × (n ≤ p)` and
`(m * n , p)` parses as `((m * n) , p)`.

Given two types `A` and `B`, we refer to `A x B` as the
*product* of `A` and `B`.  In set theory, it is also sometimes
called the *cartesian product*, and in computing it corresponds
to a *record* type. Among other reasons for
calling it the product, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A × B` has `m * n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members.
\begin{code}
data Bool : Set where
  true : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
\end{code}
Then the type `Bool × Tri` has six members:

    (true  , aa)    (true  , bb)    (true ,  cc)
    (false , aa)    (false , bb)    (false , cc)

For example, the following function enumerates all
possible arguments of type `Bool × Tri`:
\begin{code}
×-count : Bool × Tri → ℕ
×-count (true , aa) = 1
×-count (true , bb) = 2
×-count (true , cc) = 3
×-count (false , aa) = 4
×-count (false , bb) = 5
×-count (false , cc) = 6
\end{code}

Product on types also shares a property with product on numbers in
that there is a sense in which it is commutative and associative.  In
particular, product is commutative and associative *up to
isomorphism*.

For commutativity, the `to` function swaps a pair, taking `(x , y)` to
`(y , x)`, and the `fro` function does the same (up to renaming).
Instantiating the patterns correctly in `invˡ` and `invʳ` is essential.
Replacing the definition of `invˡ` by `λ w → refl` will not work;
and similarly for `invʳ`, which does the same (up to renaming).
\begin{code}
×-comm : ∀ {A B : Set} → (A × B) ≃ (B × A)
×-comm =
  record
    { to = λ { (x , y) → (y , x)}
    ; fro = λ { (y , x) → (x , y)}
    ; invˡ = λ { (x , y) → refl }
    ; invʳ = λ { (y , x) → refl }
    } 
\end{code}

Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m * n ≡ n * m
    A × B ≃ B × A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m * n` and `n * m` are equal to `6`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool × Tri` is
*not* the same as `Tri × Bool`.  But there is an isomorphism
between the two types.  For
instance, `(true , aa)`, which is a member of the former, corresponds
to `(aa , true)`, which is a member of the latter.

For associativity, the `to` function reassociates two uses of pairing,
taking `((x , y) , z)` to `(x , (y , z))`, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
\begin{code}
×-assoc : ∀ {A B C : Set} → ((A × B) × C) ≃ (A × (B × C))
×-assoc =
  record
    { to = λ { ((x , y) , z) → (x , (y , z)) }
    ; fro = λ { (x , (y , z)) → ((x , y) , z) }
    ; invˡ = λ { ((x , y) , z) → refl }
    ; invʳ = λ { (x , (y , z)) → refl }
    } 
\end{code}

Again, being *associative* is not the same as being *associative
up to isomorphism*.  For example, the type `(ℕ × Bool) × Tri`
is *not* the same as `ℕ × (Bool × Tri)`. But there is an
isomorphism between the two types. For instance `((1 , true) , aa)`,
which is a member of the former, corresponds to `(1 , (true , aa))`,
which is a member of the latter.

Here we have used lambda-expressions with pattern matching.
For instance, the term

    λ { (x , y) → (y , x) }

corresponds to the function `h`, where `h` is defined by
\begin{code}
h : ∀ {A B : Set} → A × B → B × A
h (x , y) = (y , x)
\end{code}
Often using an anonymous lambda expression is more convenient than
using a named function: it avoids a lengthy type declaration; and the
definition appears exactly where the function is used, so there is no
need for the writer to remember to declare it in advance, or for the
reader to search for the definition elsewhere in the code.

## Truth is unit

Truth `⊤` always holds. We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}
Evidence that `⊤` holds is of the form `tt`.

Given evidence that `⊤` holds, there is nothing more of interest we
can conclude.  Since truth always holds, knowing that it holds tells
us nothing additional.

We refer to `⊤` as *the unit type* or just *unit*. And, indeed,
type `⊤` has exactly once member, `tt`.  For example, the following
function enumerates all possible arguments of type `⊤`:
\begin{code}
⊤-count : ⊤ → ℕ
⊤-count tt = 1
\end{code}

For numbers, one is the identity of multiplication. Correspondingly,
unit is the identity of product *up to isomorphism*.

For left identity, the `to` function takes `(tt , x)` to `x`, and the `fro` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
\begin{code}
⊤-identityˡ : ∀ {A : Set} → (⊤ × A) ≃ A
⊤-identityˡ =
  record
    { to   = λ { (tt , x) → x }
    ; fro  = λ { x → (tt , x) }
    ; invˡ = λ { (tt , x) → refl }
    ; invʳ = λ { x → refl}
    }
\end{code}

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    1 * m ≡ m
    ⊤ × A ≃ A

In the first case, we might have that `m` is `2`, and both
`1 * m` and `m` are equal to `2`.  In the second
case, we might have that `A` is `Bool`, and `⊤ × Bool` is *not* the
same as `Bool`.  But there is an isomorphism betwee the two types.
For instance, `(tt, true)`, which is a member of the former,
corresponds to `true`, which is a member of the latter.

That unit is also a right identity follows immediately from left
identity, commutativity of product, and symmetry and transitivity of
isomorphism.
\begin{code}
⊤-identityʳ : ∀ {A : Set} → A ≃ (A × ⊤)
⊤-identityʳ = ≃-trans (≃-sym ⊤-identityˡ) ×-comm
\end{code}

[Note: We could introduce a notation similar to that for reasoning on ≡.]


## Disjunction is sum

Given two propositions `A` and `B`, the disjunction `A ⊎ B` holds
if either `A` holds or `B` holds.  We formalise this idea by
declaring a suitable inductive type.
\begin{code}
data _⊎_ : Set → Set → Set where
  inj₁  : ∀ {A B : Set} → A → A ⊎ B
  inj₂ : ∀ {A B : Set} → B → A ⊎ B
\end{code}
Evidence that `A ⊎ B` holds is either of the form
`inj₁ M`, where `M` is evidence that `A` holds, or `inj₂ N`, where
`N` is evidence that `B` holds.

Given evidence that `A → C` and `B → C` both hold, then given
evidence that `A ⊎ B` holds we can conlude that `C` holds.
\begin{code}
⊎-elim : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y
\end{code}
Pattern matching against `inj₁` and `inj₂` is typical of how we exploit
evidence that a disjunction holds.

We set the precedence of disjunction so that it binds less tightly
than any other declared operator.
\begin{code}
infix 1 _⊎_
\end{code}
Thus, `A × C ⊎ B × C` parses as `(A × C) ⊎ (B × C)`.

Given two types `A` and `B`, we refer to `A ⊎ B` as the
*sum* of `A` and `B`.  In set theory, it is also sometimes
called the *disjoint union*, and in computing it corresponds
to a *variant record* type. Among other reasons for
calling it the sum, note that if type `A` has `m`
distinct members, and type `B` has `n` distinct members,
then the type `A ⊎ B` has `m + n` distinct members.
For instance, consider a type `Bool` with two members, and
a type `Tri` with three members, as defined earlier.
Then the type `Bool ⊎ Tri` has five
members:

    (inj₁ true)     (inj₂ aa)
    (inj₁ false)    (inj₂ bb)
                    (inj₂ cc)

For example, the following function enumerates all
possible arguments of type `Bool ⊎ Tri`:
\begin{code}
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)  = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa)    = 3
⊎-count (inj₂ bb)    = 4
⊎-count (inj₂ cc)    = 5
\end{code}

Sum on types also shares a property with sum on numbers in that it is
commutative and associative *up to isomorphism*.

For commutativity, the `to` function swaps the two constructors,
taking `inj₁ x` to `inj₂ x`, and `inj₂ y` to `inj₁ y`; and the `fro`
function does the same (up to renaming). Replacing the definition of
`invˡ` by `λ w → refl` will not work; and similarly for `invʳ`, which
does the same (up to renaming).
\begin{code}
⊎-comm : ∀ {A B : Set} → (A ⊎ B) ≃ (B ⊎ A)
⊎-comm = record
  { to   = λ { (inj₁ x) → (inj₂ x)
             ; (inj₂ y) → (inj₁ y)
             }
  ; fro  = λ { (inj₁ y) → (inj₂ y)
             ; (inj₂ x) → (inj₁ x)
             }
  ; invˡ = λ { (inj₁ x) → refl
             ; (inj₂ y) → refl
             }
  ; invʳ = λ { (inj₁ y) → refl
             ; (inj₂ x) → refl
             }
  }
\end{code}
Being *commutative* is different from being *commutative up to
isomorphism*.  Compare the two statements:

    m + n ≡ n + m
    A ⊎ B ≃ B ⊎ A

In the first case, we might have that `m` is `2` and `n` is `3`, and
both `m + n` and `n + m` are equal to `5`.  In the second case, we
might have that `A` is `Bool` and `B` is `Tri`, and `Bool ⊎ Tri` is
*not* the same as `Tri ⊎ Bool`.  But there is an isomorphism between
the two types.  For instance, `inj₁ true`, which is a member of the
former, corresponds to `inj₂ true`, which is a member of the latter.

For associativity, the `to` function reassociates, and the `fro` function does
the inverse.  Again, the evidence of left and right inverse requires
matching against a suitable pattern to enable simplificition.
\begin{code}
⊎-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = record
  { to   = λ { (inj₁ (inj₁ x)) → (inj₁ x)
             ; (inj₁ (inj₂ y)) → (inj₂ (inj₁ y))
             ; (inj₂ z)        → (inj₂ (inj₂ z))
             }
  ; fro  = λ { (inj₁ x)        → (inj₁ (inj₁ x))
             ; (inj₂ (inj₁ y)) → (inj₁ (inj₂ y))
             ; (inj₂ (inj₂ z)) → (inj₂ z)
             }
  ; invˡ = λ { (inj₁ (inj₁ x)) → refl
             ; (inj₁ (inj₂ y)) → refl
             ; (inj₂ z)        → refl
             }
  ; invʳ = λ { (inj₁ x)        → refl
             ; (inj₂ (inj₁ y)) → refl
             ; (inj₂ (inj₂ z)) → refl
             }
  }
\end{code}

Again, being *associative* is not the same as being *associative
up to isomorphism*.  For example, the type `(ℕ + Bool) + Tri`
is *not* the same as `ℕ + (Bool + Tri)`. But there is an
isomorphism between the two types. For instance `inj₂ (inj₁ true)`,
which is a member of the former, corresponds to `inj₁ (inj₂ true)`,
which is a member of the latter.

Here we have used lambda-expressions with pattern matching
and multiple cases. For instance, the term

    λ { (inj₁ x) → (inj₂ x)
      ; (inj₂ y) → (inj₁ y)
      }

corresponds to the function `k`, where `k` is defined by
\begin{code}
k : ∀ {A B : Set} → A ⊎ B → B ⊎ A
k (inj₁ x) = inj₂ x
k (inj₂ y) = inj₁ y
\end{code}


## False is empty

False `⊥` never holds.  We formalise this idea by declaring
a suitable inductive type.
\begin{code}
data ⊥ : Set where
  -- no clauses!
\end{code}
There is no possible evidence that `⊥` holds.

Given evidence that `⊥` holds, we might conclude anything!  Since
false never holds, knowing that it holds tells us we are in a
paradoxical situation.

is a basic principle of logic, known in medieval times by the
latin phrase *ex falso*, and known to children through phrases
such as "if pigs had wings, then I'd be the Queen of Sheba".
\begin{code}
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()
\end{code}
Here since `⊥` is a type with no members, we indicate that it is
*never* possible to match against a value of this type by using
the pattern `()`.  In medieval times, this rule was know by the
latin name *ex falso*.  It is also known to children by phrases
such as "If pigs had wings then I'd be the Queen of Sheba".

We refer to `⊥` as *the empty type* or just *empty*. And, indeed,
type `⊥` has no members. For example, the following function
enumerates all possible arguments of type `⊥`:
\begin{code}
⊥-count : ⊥ → ℕ
⊥-count ()
\end{code}
Here, again, pattern `()` indicates that no value can match
type `⊥`.

For numbers, zero is the identity of additition. Correspondingly,
empty is the identity of sums *up to isomorphism*.

For left identity, the `to` function observes that `inj₁ ()` can never arise,
and takes `inj₂ x` to `x`, and the `fro` function
does the inverse.  The evidence of left inverse requires matching against
a suitable pattern to enable simplification.
\begin{code}
⊥-identityˡ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityˡ =
  record
    { to   = λ { (inj₁ ())
               ; (inj₂ x) → x
               }
    ; fro  = λ { x → inj₂ x }
    ; invˡ = λ { (inj₁ ())
               ; (inj₂ x) → refl
               }
    ; invʳ = λ { x → refl }
    }
\end{code}

Having an *identity* is different from having an identity
*up to isomorphism*.  Compare the two statements:

    0 + m ≡ m
    ⊥ ⊎ A ≃ A

In the first case, we might have that `m` is `2`, and both `0 + m` and
`m` are equal to `2`.  In the second case, we might have that `A` is
`Bool`, and `⊥ ⊎ Bool` is *not* the same as `Bool`.  But there is an
isomorphism betwee the two types.  For instance, `inj₂ true`, which is
a member of the former, corresponds to `true`, which is a member of
the latter.

That empty is also a right identity follows immediately from left
identity, commutativity of sum, and symmetry and transitivity of
isomorphism.
\begin{code}
⊥-identityʳ : ∀ {A : Set} → A ≃ (A ⊎ ⊥)
⊥-identityʳ = ≃-trans (≃-sym ⊥-identityˡ) ⊎-comm
\end{code}


## Implication is function

Given two propositions `A` and `B`, the implication `A → B` holds if
whenever `A` holds then `B` must also hold.  We formalise this idea in
terms of the function type.  Evidence that `A → B` holds is of the form

    λ (x : A) → N

where `N` is a term of type `B` containing as a free variable `x` of type `A`.
In other words, evidence that `A → B` holds is a function that converts
evidence that `A` holds into evidence that `B` holds.

Given evidence that `A → B` holds and that `A` holds, we can conclude that
`B` holds.
\begin{code}
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim f x = f x
\end{code}
In medieval times, this rule was known by the latin name *modus ponens*.

This rule is known by its latin name, *modus ponens*.

Implication binds less tightly than any other operator. Thus, `A ⊎ B →
B ⊎ A` parses as `(A ⊎ B) → (B ⊎ A)`.

Given two types `A` and `B`, we refer to `A → B` as the *function*
from `A` to `B`.  It is also sometimes called the *exponential*,
with `B` raised to the `A` power.  Among other reasons for calling
it the exponential, note that if type `A` has `m` distinct
memebers, and type `B` has `n` distinct members, then the type
`A → B` has `n ^ m` distinct members.  For instance, consider a
type `Bool` with two members and a type `Tri` with three members,
as defined earlier. The the type `Bool → Tri` has nine (that is,
three squared) members:

    { true → aa ; false → aa }    { true → aa ; false → bb }    { true → aa ; false → cc }
    { true → bb ; false → aa }    { true → bb ; false → bb }    { true → bb ; false → cc }    
    { true → cc ; false → aa }    { true → cc ; false → bb }    { true → cc ; false → cc }

For example, the following function enumerates all possible
arguments of the type `Bool → Tri`:
\begin{code}
→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...            | aa    | aa      = 1
...            | aa    | bb      = 2  
...            | aa    | cc      = 3
...            | bb    | aa      = 4
...            | bb    | bb      = 5
...            | bb    | cc      = 6
...            | cc    | aa      = 7
...            | cc    | bb      = 8
...            | cc    | cc      = 9  
\end{code}

Exponential on types also share a property with exponential on
numbers in that many of the standard identities for numbers carry
over to the types.

Corresponding to the law

    (p ^ n) ^ m  =  p ^ (n * m)

we have that the types `A → B → C` and `A × B → C` are isomorphic.
Both types can be viewed as functions that given evidence that `A` holds
and evidence that `B` holds can return evidence that `C` holds.
This isomorphism sometimes goes by the name *currying*.
The proof of the right inverse requires extensionality.
\begin{code}
postulate
  extensionality : ∀ {A B : Set} → {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g
  
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to   =  λ f → λ { (x , y) → f x y }
    ; fro  =  λ g → λ x → λ y → g (x , y)
    ; invˡ =  λ f → refl
    ; invʳ =  λ g → extensionality (λ { (x , y) → refl })
    }
\end{code}

Corresponding to the law

    p ^ (n + m) = (p ^ n) * (p ^ m)

we have that the types `A ⊎ B → C` and `(A → C) × (B → C)` are isomorphic.
That is, the assertion that if either `A` holds or `B` holds then `C` holds
is the same as the assertion that if `A` holds then `C` holds and if
`B` holds then `C` holds.
\begin{code}
→-distributes-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distributes-⊎ =
  record
    { to   = λ f → ( (λ x → f (inj₁ x)) , (λ y → f (inj₂ y)) ) 
    ; fro  = λ {(g , h) → λ { (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; invˡ = λ f → extensionality (λ { (inj₁ x) → refl ; (inj₂ y) → refl })
    ; invʳ = λ {(g , h) → refl}
    }
\end{code}

Corresponding to the law

    (p * n) ^ m = (p ^ m) * (n ^ m)

we have that the types `A → B × C` and `(A → B) × (A → C)` are isomorphic.
That is, the assertion that if either `A` holds then `B` holds and `C` holds
is the same as the assertion that if `A` holds then `B` holds and if
`A` holds then `C` holds.  The proof requires that we recognise the eta
rule for products, which states that `(fst w , snd w) ≡ w` for any product `w`.
\begin{code}
postulate
  η-× : ∀ {A B : Set} → ∀ (w : A × B) → (fst w , snd w) ≡ w

→-distributes-× : ∀ {A B C : Set} → (A → B × C) ≃ ((A → B) × (A → C))
→-distributes-× =
  record
    { to   = λ f → ( (λ x → fst (f x)) , (λ y → snd (f y)) ) 
    ; fro  = λ {(g , h) → (λ x → (g x , h x))}
    ; invˡ = λ f → extensionality (λ x → η-× (f x))
    ; invʳ = λ {(g , h) → refl}
    }
\end{code}


## Distribution

Products distributes over sum, up to isomorphism.  The code to validate
this fact is similar in structure to our previous results.
\begin{code}
×-distributes-⊎ : ∀ {A B C : Set} → ((A ⊎ B) × C) ≃ ((A × C) ⊎ (B × C))
×-distributes-⊎ =
  record
    { to   = λ { ((inj₁ x) , z) → (inj₁ (x , z)) 
               ; ((inj₂ y) , z) → (inj₂ (y , z))
               }
    ; fro  = λ { (inj₁ (x , z)) → ((inj₁ x) , z)
               ; (inj₂ (y , z)) → ((inj₂ y) , z)
               }
    ; invˡ = λ { ((inj₁ x) , z) → refl
               ; ((inj₂ y) , z) → refl
               }
    ; invʳ = λ { (inj₁ (x , z)) → refl
               ; (inj₂ (y , z)) → refl
               }               
    }
\end{code}

Sums to not distribute over products up to isomorphism, but it is an embedding.
\begin{code}
⊎-distributes-× : ∀ {A B C : Set} → ((A × B) ⊎ C) ≲ ((A ⊎ C) × (B ⊎ C))
⊎-distributes-× =
  record
    { to   = λ { (inj₁ (x , y)) → (inj₁ x , inj₁ y)
               ; (inj₂ z)       → (inj₂ z , inj₂ z)
               }
    ; fro  = λ { (inj₁ x , inj₁ y) → (inj₁ (x , y))
               ; (inj₁ x , inj₂ z) → (inj₂ z)
               ; (inj₂ z , _ )     → (inj₂ z)
               }
    ; invˡ = λ { (inj₁ (x , y)) → refl
               ; (inj₂ z)       → refl
               }
    }
\end{code}
Note that there is a choice in how we write the `fro` function.
As given, it takes `(inj₂ z , inj₂ z′)` to `(inj₂ z)`, but it is
easy to write a variant that instead returns `(inj₂ z′)`.  We have
an embedding rather than an isomorphism because the
`fro` function must discard either `z` or `z′` in this case.

In the usual approach to logic, both of the distribution laws
are given as equivalences, where each side implies the other:

    A & (B ∨ C) ⇔ (A & B) ∨ (A & C)
    A ∨ (B & C) ⇔ (A ∨ B) & (A ∨ C)

But when we consider the two laws in terms of evidence, where `_&_`
corresponds to `_×_` and `_∨_` corresponds to `_⊎_`, then the first
gives rise to an isomorphism, while the second only gives rise to an
embedding, revealing a sense in which one of these laws is "more
true" than the other.


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false. 
\begin{code}
¬_ : Set → Set
¬ A = A → ⊥
\end{code}
This is a form of *proof by contradiction*: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ (x : A) → N

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
\begin{code}
¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬a a = ¬a a
\end{code}
Here we write `¬a` for evidence of `¬ A` and `a` for evidence of `A`.  This
means that `¬a` must be a function of type `A → ⊥`, and hence the application
`¬a a` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but more tightly than anything else.
\begin{code}
infix 3 ¬_
\end{code}
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)`.

In *classical* logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use *intuitionistic* logic, wher
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
\begin{code}
¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro a ¬a = ¬a a
\end{code}
Let `a` be evidence of `A`. We will show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬a` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction (evidenced by `¬a a`).  Hence, we have
shown `¬ ¬ A`.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
\begin{code}
¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬a a = ¬¬¬a (¬¬-intro a)
\end{code}
Let `¬¬¬a` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `a` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A` (evidenced by `¬¬-intro a`).  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction (evidenced by
`¬¬¬a (¬¬-intra a)`.  Hence we have shown `¬ A`.

Another law of logic is the *contrapositive*,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
\begin{code}
contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition a→b ¬b a = ¬b (a→b a)
\end{code}
Let `a→b` be evidence of `A → B` and let `¬b` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence
`¬ A` must hold. Let `a` be evidence of `A`.  Then from `A → B` and
`A` we may conclude `B` (evidenced by `a→b a`), and from `B` and `¬ B`
we may conclude `⊥` (evidenced by `¬b (a→b a)`).  Hence, we have shown
`¬ A`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  =  1,  if n = 0
           =  0,  if n ≠ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.
\begin{code}
id : ⊥ → ⊥
id x = x
\end{code}
However, there are no possible values of type `Bool → ⊥`,
or of any type `A → ⊥` where `A` is not the empty type.






## Decidability

\begin{code}
data Dec : Set → Set where
  yes : ∀ {A : Set} → A → Dec A
  no  : ∀ {A : Set} → (¬ A) → Dec A
\end{code}



## Intuitive and Classical logic

## Universals

## Existentials

## Equivalence

## Unicode

This chapter introduces the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    
