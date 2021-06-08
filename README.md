# Mechanized Proofs of a Well-typed Store
## Still under development

The embedding of a standard PL (referred to as the monadic language or source language) into Karl Crary (@kcrary)'s new PL (referred to as the target language), 
and the verification that well-typed terms in the monadic language translate to well-typed terms in the target language. 

The monadic language is a variant of the simply typed lambda calculus with the addition of
1) the delayed compuation monad
2) a global store and general references

The embedding uses a possible worlds model to keep track of the changing type of the memory store. As such, all terms in the source language are translated 'at a given world'.
This is inspired by Pottier's 'A Typed Store-Passing Translation for General References'.

Files are, in order of importance:

Quite important:
- proofs: proof of the well-typedness of the translation and other crucial properties
- trans: translation of source terms to target terms
- rules_src: typing of monadic language
- source: grammar of monadic language

Somewhat important:
- embedded_lemmas: useful, often simple, properties of the embedding
- derived_rules: type deduction rules that are easier to use than those defining Crary's PL
- subst_help: management of De Bruijn Indices in more complex terms, lemmas for shuffling the order of dependently typed variables in a context
- help: useful terms/patterns that show up often in other files

Less important:
- subst_help0
- basic_types
- lemmas0
- tactics
