# Mechanized Proofs of a Well-typed Store
## Still under development

This development is done under the mentorship of [Karl Crary](http://www.cs.cmu.edu/~crary/) (@kcrary).

It embeds [Iota](https://github.com/misstaggart/monad_interpreter "Iota development") into a new computational logic designed for reasoning about imperative programs. This logic can be thought of as a purely functional programming language, and is referred to below as the target language. In this development, I also verify that well-typed terms in Iota translate to well-typed terms in the target language. 

At a higher level, these proofs show that our logic is sufficiently expressive to support easy reasoning about standard imperative programs.

Notable features of the embedding are:
- We use a Kripke possible worlds model for the translation of source types. This allows us to instantiate a type at the current global state and reflects the fact that the type of a source term may depend on what is currently in the store. This is inspired by Pottier's semantic types in *A Typed Store-Passing Translation for General References*.
- We use a recursive type to represent the type of the store. This reflects the fact that the store is a self-referential value; it may contain references which themselves refer to the same store. This recursive type does not exist in arbitrary semantics. To force the existence of the desired fixpoint, we use metric space semantics for our logic. Here, we take inspiration from Birkedal et al.’s *Realisability semantics of parametric polymorphism, general references, and recursive types*.

Files are, in order of importance:

Quite important:
- proofs: proof of well-typedness and other crucial properties of the embedding
- trans: translation of source terms to target terms
- rules_src: model of Iota’s type-checker
- source: model of Iota’s syntax

Somewhat important:
- embedded_lemmas: useful, often simple, properties of the embedding
- derived_rules: type deduction rules that are easier to use than those defining the target language
- subst_help: management of De Bruijn indices in more complex terms, lemmas for shuffling the order of dependently typed variables in a context
- help: useful terms/patterns that show up often in other files

Less important:
- subst_help0
- basic_types
- lemmas0
- tactics
