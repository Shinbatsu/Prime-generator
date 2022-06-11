# Prime Generation in Agda

This project implements **prime number generation** in Agda using **coinductive sorted streams** and well-founded recursion over a strict total order.

## Overview

The core idea is to represent sequences of numbers satisfying a predicate (e.g. "is prime") as an infinite, **sorted stream** with the ability to construct new streams by merging, filtering, and subtracting them based on logical conditions.

The `SortedStream` module provides:

- A definition of a stream of sorted elements.
- Proofs that each element satisfies a predicate and is greater than all previous elements.
- A mechanism for well-founded recursion to build streams safely.

## Key Concepts

### `IsMinimal`
```agda
IsMinimal : ∀ {A} → (P : Pred A Level.zero) (_<_ : A → A → Set) → Pred A Level.zero
```
An element `x` is minimal if no smaller element `y` also satisfies the predicate `P`.

---

### `Minimum`
```agda
record Minimum {A} (P : Pred A Level.zero) (_<_ : A → A → Set) : Set where
constructor minimum
field
    value : A
    holds : P value
    isMin : IsMinimal P _<_ value
```
A `Minimum` bundles an element `value` together with:
- A proof that it satisfies the predicate `P`.
- A proof that it is minimal with respect to `<`.

---

### `SortedStream`
```agda
record SortedStream {A} (_<_ : A → A → Set) (P : A → Set) (b : Maybe A) : Set where
inductive
constructor _∷_
field
    headd : Minimum (Good P _<_ b) _<_
    taill : ∞ (SortedStream _<_ P (just (Minimum.value headd)))
```

A `SortedStream` is a **coinductive structure** that:
- Has a head (`headd`) which is the minimal next element.
- Lazily produces the tail (`taill`) of the stream.
- Maintains a lower bound `b` to ensure elements are generated in sorted order.

---

### Aux Definitions

- `None P < lb ub`  
Proof that no element between `lb` and `ub` satisfies `P`.

- `Good P < bnd x`  
Proof that `x` satisfies `P` and is above the bound `bnd`.

- `Bounded->`  
Defines a relation for well-founded recursion within bounds.

---

## WithTotalOrder Module

The `WithTotalOrder` module provides utilities to work under a **strict total order** with well-foundedness:

- `extend-isMinimal`  
Extends a minimality proof when the lower bound changes.

- `m>-wf`  
Proves well-foundedness of the bounded relation.

- `subtract-step`  
A recursive step for subtracting one sorted stream from another (used for operations like "filtering out multiples" in prime generation).

- `subtract`  
High-level stream subtraction based on `subtract-step`.

These tools allow building infinite sorted streams of primes by starting from natural numbers and recursively filtering out composites.

---

## Prime Generation Methods

The prime generation is built upon:

- **Base stream**: Start with an infinite sorted stream of natural numbers greater than `1`.
- **Prime extraction**: The minimal element of the stream is taken as the next prime.
- **Stream subtraction**: Multiples of the prime are removed using `subtract`.
- **Recursive definition**: Coinductive construction continues infinitely to yield the complete prime stream.
