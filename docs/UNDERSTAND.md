# Understanding Soma

This document aims to provide a comprehensive understanding of the theoretical foundations behind Soma, a programming language based on interaction combinators. We will explore the historical context of programming languages, the principles of linear logic, the concept of interaction nets, and finally, the specifics of interaction combinators.

Then, we will discuss how Soma leverages these concepts to offer a unique programming experience, focusing on its practical applications and advantages.

Table of contents:
1. [Historical Context](#historical-context)
  1.1 [Models of Computation](#models-of-computation)
  1.2 [Linear Logic](#linear-logic)
  1.3 [Interaction Nets](#interaction-nets)
  1.4 [Interaction Combinators](#interaction-combinators)
  1.5 [Interaction Calculus](#interaction-calculus)
  1.6 [TL;DR](#tldr)
2. [Where Soma Comes In](#where-soma-comes-in)
  2.1 [A Language You Can Actually Use](#a-language-you-can-actually-use)
  2.2 [No Garbage Collection](#no-garbage-collection)
  2.3 [Strict Evaluation with Optimal Sharing](#strict-evaluation-with-optimal-sharing)
  2.4 [Parallelism for Free](#parallelism-for-free)
  2.5 [Why This Matters for You](#why-this-matters-for-you)
3. [Acknowledgments](#-acknowledgments)

# Historical Context

## Models of Computation

Along the history of computer science, programming languages have revolved around two models of computation:

1. **Turing Machines**: These are abstract machines that manipulate symbols on a strip of tape according to a set of rules. They are used to model algorithmic processes and are foundational in the theory of computation.

> Examples: Python, Java, C++, and many other imperative and object-oriented programming languages are based on the Turing machine model. They focus on changing state through statements and control structures.

2. **Lambda Calculus**: This is a formal system for expressing computation based on function abstraction and application. It serves as the theoretical foundation for functional programming languages.

> Examples: Haskell, Lisp, and Erlang are examples of functional programming languages that are based on the principles of lambda calculus. They emphasize the use of functions and immutability.

However, there are significant downsides to both. Turing machine-based languages can lead to complex state management and side effects, making reasoning about programs difficult. On the other hand, while lambda calculus-based languages promote cleaner abstractions, they can struggle with side effects and stateful computations, which are often necessary in real-world applications.

That is because functional programming languages are very inspired by the Curry-Howard correspondence, which establishes a direct relationship between computer programs and mathematical proofs. In Curry-Howard, types are propositions and functions are proofs. For ex, `id : A -> A` is a proof that from proposition A, we can derive proposition A. This correspondence encourages a view of programming as constructing proofs, leading to a focus on pure functions and immutability.

But there have been significant criticisms of classical and intuitionistic logic, which underpin much of functional programming. That is because they assume no resource management!

Functional programming is often avoided because they're perceived as inefficient in terms of resource usage, particularly memory and processing power. This is because functional programming languages often rely on immutable data structures and recursion, which can lead to increased memory consumption and slower performance compared to imperative languages that use mutable state and iterative constructs.

In classical/intuitionistic logic, assumptions can be used freely and discarded after use. This is not reflective of real-world scenarios where resources are often limited and must be managed carefully. For example, if you have a file handle or a network connection, you can't just use it once and discard it; you need to ensure it's properly closed or released after use.

## Linear logic

Linear logic, introduced by Jean-Yves Girard in 1987, addresses these issues by treating assumptions as resources that must be used exactly once. This means that if you have a resource, you must use it in your computation, and you cannot simply discard it or duplicate it without explicit permission.

This is what led to the development of linear type systems in programming languages such as Rust. Rust's ownership model is a practical implementation of linear logic principles. In Rust, each value has a single owner, and when the owner goes out of scope, the value is automatically deallocated. This ensures that resources are managed efficiently and safely, preventing issues like memory leaks and data corruption.

As a bonus, linear logic also has built-in mechanisms for concurrency and parallelism. Since resources must be used exactly once, it naturally leads to a model where computations can be performed in parallel without the risk of race conditions or data corruption.

> Note: it doesn't have anything to do with linear algebra or linear equations!

## Interaction Nets

After linear logic was theorized, several researchers realized it could model functional computation with the bonus of fine-grained resource management. This led to variants of lambda calculus, and the development of Interaction Nets by Yves Lafont in 1990.

The core idea of Interaction Nets is to represent computations as a network of interconnected nodes, where each node represents a computational operation, and the edges represent the flow of data between these operations. The key feature of Interaction Nets is that they allow for local interactions between nodes, meaning that computations can be performed in parallel without the need for a global control structure.

The key link to linear logic is that interaction nets can naturally encode linear logic proof nets (a graphical representation of proofs in linear logic). Each interaction in the net corresponds to a logical inference, and the structure of the net reflects the resource management principles of linear logic.

Interaction nets are basically:
1. A set of agents (nodes) with ports
2. A set of wires connecting the ports
3. An evaluator that applies interaction rules to pairs of connected agents

If two agents are connected via their principal ports, they can interact according to predefined rules, transforming the net.

Think of it like this: principal ports represent how a node is used by other nodes and show the flow of computation that depends on this node. Auxiliary ports, on the other hand, carry the information the node needs to exist or compute, encoding the inputs required for the node to do its work.

```Haskell
let x = 5 in x + 10
```

Here, the interaction nets visualization is:

```
  [let]
  /   \ 
[5]    [+]
       / \
    (x)   [10]
     |
    [5]
```

## Interaction Combinators

Also developed by Yves Lafont in 1997, his goal with Interaction Combinators was to find the simplest possible universal interaction system. He achieved this with just three types of agents:

1. **γ (gamma):** the constructor. It builds and deconstructs data structures like pairs, lists, or tree nodes.
2. **δ (delta):** the duplicator. It copies data when a value needs to be used more than once.
3. **ε (epsilon):** the eraser. It garbage-collects data that's no longer needed.

These agents interact according to simple rules when they meet via their principal ports:

- **Annihilation (γ-γ or δ-δ):** When two agents of the same type collide, they cancel out and their auxiliary wires connect directly. Think of it like a constructor meeting a destructor—they undo each other.

- **Commutation (γ-δ):** When a constructor meets a duplicator, they "pass through" each other. The duplicator clones the constructor, and the constructor splits the duplicator. This is how copying propagates through a data structure.

- **Erasure (ε-anything):** When an eraser meets any agent, it destroys that agent and spawns erasers for each of its auxiliary ports. Garbage collection cascades through the structure.

What makes this system remarkable is its universality: these three agents and their interaction rules are sufficient to encode any computation. Any Turing machine, any lambda calculus term, any algorithm can be represented and executed using just γ, δ, and ε.

The beauty lies in the locality and parallelism. Each interaction only involves two agents and their immediate connections. This means no global state, no shared memory, no synchronization needed. Any two independent interactions can happen simultaneously. This makes interaction combinators an ideal foundation for massively parallel computation.

To quote Victor Taelin's (Soma is only possible because of his research and public work which made me learn all of this)'s words: 

> "Interestingly, every aspect which is considered good in other models of computation is present on Interaction Combinators, while negative aspects are almost entirely absent. Moreover, both the Lambda Calculus and the Turing Machine can be efficiently emulated by the Interaction Combinators, while the opposite isn't true. This suggests that, while the 3 systems are equivalent in terms of computability, the Interaction Combinators are more capable in terms of computation. Under certain point of view, one could argue that both the Turing Machine and the Lambda Calculus are slight distortions of this fundamental model, caused by human creativity, due to our historical intuitions regarding machines and mathematics. Perhaps machines and substitutions aren't as fundamental as we think, and some alien civilization has developed all its mathematical theories and computers based on annihilation and commutation, with no references to the Lambda Calculus, or the Turing Machine."

This is my favourite quote about Interaction Combinators because it perfectly summarizes why I believe they are the future of computation.

## Interaction Calculus

While interaction combinators are universal and elegant, they're low-level—like writing assembly for computation graphs. Programming directly with γ, δ, and ε is tedious. What we need is a higher-level language that compiles down to interaction combinators.

This is where the Interaction Calculus (IC), also developed by Victor Taelin, comes in. It's essentially lambda calculus redesigned from the ground up to map naturally onto interaction nets. The result is a calculus that looks familiar to functional programmers but has radically different semantics.

Three key changes distinguish IC from traditional lambda calculus:

1. **Affine variables:** Each variable can be used at most once. This directly reflects the linear logic foundation—every value is a resource that must be consumed exactly once (or explicitly discarded).

2. **Global scoping:** Variables aren't bound to their lexical scope. They can appear anywhere in the program. This sounds chaotic, but it's actually what enables optimal sharing.

3. **Superpositions and duplications:** When you need to use a value more than once, you don't just copy it. Instead, you create a *superposition*—a value that exists in multiple "branches" simultaneously. A *duplication* then collapses these branches when needed.

The superposition/duplication mechanism is what makes IC special. In normal lambda calculus, if you write `let x = expensive() in x + x`, the term `expensive()` might be computed twice. Optimal evaluators solve this through complex bookkeeping. In IC, the solution is built into the language itself: `expensive()` becomes a superposition that's shared between both uses, and duplication happens lazily (or in Soma's case, eagerly) only when the values actually need to diverge.

This gives IC something remarkable: *optimal evaluation* by construction. The interaction net representation automatically shares computation in the most efficient way possible, avoiding redundant work that plagues traditional functional languages.

The tradeoff is that IC can't express certain lambda calculus terms—notably self-application like `λx.(x x)`, since that would require using `x` twice. But in practice, this restriction eliminates the patterns that cause exponential blowup in evaluation, turning them into the efficient shared computation that interaction nets excel at.

## TL;DR

- Traditional programming languages are based on Turing machines (imperative) or lambda calculus (functional), both of which have limitations in resource management and parallelism.
- Linear logic treats assumptions as resources that must be used exactly once, leading to better resource management
- Interaction nets represent computations as networks of nodes that interact locally, allowing for parallelism and efficient resource usage.
- Interaction combinators are a minimal universal system using just three types of agents (constructor, duplicator, eraser) that can represent any computation through local interactions.
- Interaction calculus is a higher-level language that maps onto interaction nets, using affine variables, global scoping, and superpositions to achieve optimal evaluation by construction.

# Where Soma Comes In

Everything above: linear logic, interaction nets, interaction combinators, interaction calculus—is beautiful theory. But theory doesn't ship products, you can't tell a company "just rewrite your codebase in interaction combinators bro trust me". The gap between theoretical elegance and practical programming has kept these ideas confined to academic papers for decades.

Soma bridges that gap.

## A Language You Can Actually Use

Soma is a statically-typed, pure functional language with Hindley-Milner type inference. If you've used Haskell, OCaml, or even TypeScript with strict settings, you'll feel at home. You write normal functional code: pattern matching, higher-order functions, algebraic data types—and the compiler handles everything else.

The key insight is that *you never see the interaction nets*. You don't write DUP nodes or think about superpositions. The compiler analyzes your code, infers where values need to be duplicated or erased, and generates the optimal interaction net representation automatically. It's the difference between writing assembly and writing Python. Except here, you get Python's expressiveness with assembly's performance.

## No Garbage Collection

This is Soma's headline feature, and it deserves emphasis: **Soma has no garbage collector**. Nor does it require manual memory management or constantly fighting a borrow checker.

Most functional languages pay a steep runtime tax. Haskell has a sophisticated generational GC that can pause your program unpredictably. OCaml's GC is fast but still introduces latency spikes. Even Rust, which avoids GC, makes you wrestle with lifetimes and ownership rules.

Soma takes a different path. After the compiler linearizes your code, every value has exactly one owner and is used exactly once. When a value is consumed, it's freed immediately. Not "eventually" by a background thread, not "when the GC gets around to it," but *right then*. Memory management is as predictable as a `free()` call in C, but you never write it yourself.

This matters for real-time systems, games, trading systems and anywhere unpredictable pauses are unacceptable. But it also matters for regular applications: no GC tuning, no memory bloat, no "why is my program suddenly slow?" debugging sessions.

## Strict Evaluation with Optimal Sharing

Here's where Soma diverges from other interaction net implementations like HVM (also by Victor Taelin's HOC).

HVM uses lazy evaluation. This is theoretically elegant since it maximizes sharing and achieves Lamping-style optimal reduction. But laziness introduces unpredictability and overhead. A seemingly innocent expression might build up a massive thunk that explodes when finally evaluated. Besides, if a thunk captures a lot of context, it can bloat memory usage. Space leaks are notoriously hard to debug.

> Laziness means that expressions are not evaluated until their results are needed. So for the code `print(5 + 5)`, instead of it becoming `print(10)` immediately, it creates a "thunk" representing the unevaluated expression `5 + 5`. Only when `print` tries to use that value does the addition actually get computed.

Soma uses strict (call-by-value) evaluation. This means that, when you call a function, its argument is evaluated first. What you see is what you compute. This makes performance predictable and reasoning about your code straightforward.

But as HOC's research shows, Lamping-style theoretical optimal evaluation requires laziness. So you might think: isn't CBV the wrong move here? Well, my goal from the start was to make a CBV language because I dislike Haskell's laziness. So I thought "why not attempt eager duplications". And they work and remove the downsides of laziness that I dont like: unpredictability and overhead by sacrificing theoretical optimality.

The compiler still uses interaction nets internally, still inserts DUP nodes for shared computation, still avoids redundant work. You get the *benefits* of optimal reduction (no recomputation of shared subexpressions) without the *costs* of laziness (unpredictable evaluation order, space leaks).

It's a pragmatic middle ground: predictable semantics for the programmer, optimal execution under the hood.

## Parallelism for Free

Remember how interaction nets allow independent reductions to happen simultaneously? If not, this is what interaction nets bring to you: free parallelism. Since there are no side effects and no shared state, any two parts of your computation that don't depend on each other can be evaluated in parallel.

The language has three modes:
1. **standard:** default, predictable runtime (no laziness or implicit parallelism)
2. **graph:** everything that can be parallelized, will be parallelized without any extra code from you
3. **hybrid:** same runtime as the standard mode but with fork-join parallelism for expensive computations

In graph mode, the compiler generates code that runs on a work-stealing parallel runtime. Independent parts of your computation (branches of a recursive tree, elements of a map operation, etc.) are automatically distributed across CPU cores. No threads to manage, no locks to debug, no race conditions to fear.

On a simple fibonacci benchmark, Soma achieves **8.77x speedup with 4 workers**—that's super-linear scaling, better than the theoretical maximum, because the distributed workload fits better in per-core caches. And you didn't write a single line of parallel code.

This is simply the natural consequence of building on interaction nets. When your computation model is inherently local and interference-free, parallelism becomes a free bonus rather than a hard problem.

## Why This Matters for You

If you're a CS student reading this, you might be wondering: why should I care about yet another programming language?

For 80+ years, we've built programming languages on two models: Turing machines (imperative programming) and lambda calculus (functional programming). Both have deep flaws. Imperative code is hard to reason about and slow to code (otherwise everyone would be using ASM and no one would use Go). Functional code is perceived as slow and memory-hungry.

Interaction nets offer a third way that's mathematically cleaner than both, inherently parallel, and memory-efficient by construction. But until now, this has been locked away in papers that only PhD students read.

Soma is an attempt to make these ideas accessible and, ultimately, to prove that you can have functional programming's expressiveness, systems programming's performance, and automatic parallelism all in one language, without sacrificing usability. As a big fan of both functional programming and systems programming, this is simply an attempt to create my dream language.

My main reason for writing this document is to invite people who will care about this project as much as I do. Who will be enthusiastic about building a new kind of programming language from the ground up, based on solid theoretical foundations and have a programming language to call their own.

The future of computation might not be Turing machines or lambda calculus. It might be annihilation and commutation. And you could help build it!

# 🙏 Acknowledgments

Special thanks to **HigherOrderCo** (HOC) and **Victor Taelin** for their groundbreaking research and development in Interaction Nets and Interaction Calculus. Their work on optimal evaluation, the HVM runtime, and the theoretical foundations of interaction-based computation has been instrumental in developing Soma's Circuit IR (the part of the compiler that lowers code to interaction calculus) and runtime system.
