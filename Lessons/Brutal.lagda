----
author: Jan Malakhovski
id: 20121219
tags: fp, agda, dependent types, logic
----

# Brutal [Meta]Introduction to Dependent Types in Agda

## Introduction to introduction

Agda doesn't lack tutorials and introductions, there is a whole page of them on the Agda wiki [@agda-tutorials] (for a general documentation list see [@agda-documentation]).
Personally, I recommend:

* Anton Setzer's introduction (works especially very well for those with a logical background, but is easy enough to follow for everyone else too) [@Setzer:interactive-theorem-proving]
* Ana Bove's and Peter Dybjer's introduction [@Bove-Dybjer:deptypes-at-work].
* Ulf Norell's introduction for functional programmers [@Norell:afp08-tutorial].
* Thorsten Altenkirch's lectures [@Altenkirch:computer-aided-formal-reasoning-course].

(This list is not an order, the best practice is to read them (and this page) simultaneously.
By the way, this document is far from finished, but should be pretty useful in its current state.)

Same proposition holds for Coq [@coq-documentation], Idris [@idris-documentation] and, to a lesser extent, for Epigram [@epigram-documentation].

For a general introduction to type theory field look no further than:

* Morten Heine B. SÃ¸rensen's and Pawel Urzyczyn's lectures [@Sorensen-Urzyczyn:lectures-on-curry-howard-isomorphism:1998].
* Simon Thompson's book [@Thompson:TTFP].

There's also a number of theoretical books strongly related to the languages listed above:

* The notes of Per Martin-LÃ¶f's (the author of the core type theory used by all of Agda, Coq, Idris and Epigram) lectures [@MartinLoef:ITT-Sambin;@MartinLoef:ITT].
* A bit more practical-oriented book by Bengt NordstrÃ¶m et al [@Nordstoem:programming-in-MLTT].

And a number of tutorials which show how to implement a dependently typed language yourself:

* "Simpler Easier" [@augustss:simpler-easier].
* A tutorial by Andrej Bauer [@Bauer:implement-deptypes-1;@Bauer:implement-deptypes-2;@Bauer:implement-deptypes-3].

There's a lot to read already, why another introduction?
Because there is a gap.
Theory is huge and full of subtle details that are mostly ignored in tutorial implementations and hidden in language tutorials (so that unprepared are not scared away).
Which is hardly surprising since the current state of art takes years to implement correctly, and even then some (considerable) problems remain.

Nevertheless, I think it is the hard parts that matter, and I always wanted a tutorial that at least mentioned their existence (well, obviously there is a set of dependently typed problems most people appreciate, e.g. undecidable type inference, but there is still a lot of issues that are not so well-understood).
Moreover, after I stumbled upon some of these lesser known parts of dependently typed programming I started to suspect that hiding them behind the language goodnesses actually makes things _harder_ to understand.
"Dotted patterns" and "unification stuck" error in Agda are perfect examples.
I claim that:

* People find it hard to understand "dotted patterns" exactly because it's hard to explain them above the language abstraction level.
* Explicit access to unification engine is a useful interactive program construction tool.
I did a dozen of proofs I probably couldn't do otherwise by unifying expressions by hand.
As far as I'm aware, no proof checker automates this in a usable way yet.
There is [a proposal](http://code.google.com/p/agda/issues/detail?id=771) with my implementation ideas for `agda2-mode`.

Having said that, this article serves somewhat controversial purposes:

* It is a introduction to Agda, starting as a very basic one, written for those with half-way-through-undergrad-course (read "basic") discrete math, number theory, set theory and Haskell background.
I actually taught this to undergrad students [@Me:itmo-functional-programming-and-proof-checking-course] and it works.
* But it aims not to teach Agda, but to show how dependently typed languages work behind the scenes without actually going behind the scenes (because, as noted above, going behind the scenes takes years).
I'm pretty sure it is possible to write a very similar introduction to Coq, Idris, Epigram or whatever, but Agda works perfectly because of its syntax and heavy unification usage.
* There is also a number of *[italicized comments in brackets]* laying around, usually for those with type theory background. Don't be scared, you can completely ignore them. They give deeper insights if you research on them, though.
* The last two sections contain completely type theoretic stuff. They are the reason I started writing this, but, still, you may ignore them completely if you wish.
* You are expected to understand everything else.
Do exercises and switch to other tutorials when stuck.

Finally, before we start, a disclaimer: I verified my core thoughts about how all this stuff works by reading (parts of) Agda's source code, but still, as Plato's Socrates stated, "I know that I know nothing".

## Slow start

### You want to use Emacs, trust me

There is *agda2-mode* for Emacs. It allows to:

* input funny UNICODE symbols like â„• or Î£,
* interactively interact with Agda (more on that below).

Installation:

* install `emacs`,
* install everything with `agda` substring from your package manager or `Agda` and `Agda-executable` with `cabal`,
* run `agda-mode setup`.

Running:

* run `emacs`,
* press `C-x C-f FileName RET` (Control+x, Control+f, type "FileName", press Return/Enter key).

Note that you can load [this article in Literate Agda format](../BrutalDepTypes.lagda) directly into Emacs.
This is actually a recommended way to use this text, you can't do exercises in HTML version.

### Syntax

In Agda a module definition always goes first:
\begin{code}
module BrutalDepTypes where
\end{code}

Nested modules and modules with parameters are supported.
One of the most common usages of nested modules is to hide some definitions from the top level namespace:

\begin{code}
module ThrowAwayIntroduction where
\end{code}

Datatypes are written in GADTs-style:
\begin{code}
  data Bool : Set where
    true false : Bool -- Note, we can list constructors of a same type
                      -- by interspersing them with spaces.
    
  -- input for â„• is \bn,
  -- input for â†’ is \to, but -> is fine too
  -- Naturals.
  data â„• : Set where
    zero : â„•
    succ : â„• â†’ â„•
  
  -- Identity container
  data Id (A : Set) : Set where
    pack : A â†’ Id A
    
  -- input for âŠ¥ is \bot
  -- Empty type. Absurd. False proposition.
  data âŠ¥ : Set where
\end{code}
`Set` here means the same thing as kind `*` in Haskell, i.e. a type of types (more on that below).

Agda is a total language.
There is no `undefined`,  all functions are guaranteed to terminate on all possible inputs (if not explicitly stated otherwise by a compiler flag or a function definition itself), which means that `âŠ¥` type is really empty.

Function declarations are very much like in Haskell:
\begin{code}
  -- input for â‚€ is \_0, â‚ is \_1 and so on
  idâ„•â‚€ : â„• â†’ â„•
  idâ„•â‚€ x = x
\end{code}
except function arguments have their names even in type expressions:
\begin{code}
  -- Note, argument's name in a type might differ from a name used in pattern-matching
  idâ„•â‚ : (n : â„•) â†’ â„•
  idâ„•â‚ x = x -- this `x` refers to the same argument as `n` in the type
\end{code}
with `idâ„•â‚€`'s definition being a syntax sugar for:
\begin{code}
  idâ„•â‚‚ : (_ : â„•) â†’ â„•
  idâ„•â‚‚ x = x
\end{code}
where the underscore means "I don't care about the name", just like in Haskell.

Dependent types allow type expressions after an arrow to depend on expressions before the arrow,
this is used to type polymorphic functions:
\begin{code}
  idâ‚€ : (A : Set) â†’ A â†’ A
  idâ‚€ _ a = a
\end{code}
Note that this time `A` in the type cannot be changed into an underscore, but it's fine to ignore this name in pattern matching.

Pattern matching looks as usual:
\begin{code}
  not : Bool â†’ Bool
  not true  = false
  not false = true
\end{code}
except if you make an error in a constructor name:
\begin{code}
  notâ‚€ : Bool â†’ Bool
  notâ‚€ true  = false
  notâ‚€ fals  = true
\end{code}
Agda will say nothing.
This might be critical sometimes:
\begin{spec}
  data Three : Set where
    COne CTwo CThree : Three

  three2â„• : Three â†’ â„•
  three2â„• COne = zero
  three2â„• Ctwo = succ zero
  three2â„• _    = succ (succ zero) -- intersects with the previous clause
\end{spec}

Finally, Agda supports implicit arguments:
\begin{code}
  id : {A : Set} â†’ A â†’ A
  id a = a

  idTestâ‚€ : â„• â†’ â„•
  idTestâ‚€ = id
\end{code}
Values of implicit arguments are derived from other arguments' values and types by solving type equations (more on them below).
You don't have to apply them or pattern match on them explicitly, but you still can if you wish:
\begin{code}
  -- positional:
  idâ‚ : {A : Set} â†’ A â†’ A
  idâ‚ {A} a = a

  idTestâ‚ : â„• â†’ â„•
  idTestâ‚ = id {â„•}

  -- named:
  constâ‚€ : {A : Set} {B : Set} â†’ A â†’ B â†’ A
  constâ‚€ {B = _} a _ = a

  constTestâ‚€ : â„• â†’ â„• â†’ â„•
  constTestâ‚€ = constâ‚€ {A = â„•} {B = â„•}
\end{code}

*[It's important to note that no proof search is ever done.
Implicit arguments are completely orthogonal to computational aspect of a program, being implicit doesn't imply anything else.
Implicit variables are not treated any way special, they are not type-erased any way differently than others.
They are just a kind of syntax sugar assisted by equation solving.]*

It's allowed to skip arrows between arguments in parentheses or braces:
\begin{code}
  idâ‚ƒ : {A : Set} (a : A) â†’ A
  idâ‚ƒ a = a
\end{code}
and to intersperse names of values of the same type by spaces inside parentheses and braces:
\begin{code}
  const : {A B : Set} â†’ A â†’ B â†’ A
  const a _ = a
\end{code}

What makes Agda's syntax so confusing is the usage of underscore.
In Haskell "I don't care about the name" is the only meaning for it, in Agda there are another two and a half.
The first one being "guess the value yourself":
\begin{code}
  idTestâ‚ƒ : â„• â†’ â„•
  idTestâ‚ƒ = idâ‚€ _
\end{code}
which works exactly the same way as implicit arguments.

Or, to be more precise, it is the implicit arguments that work like arguments implicitly applied with underscores, except Agda does this once for each function definition, not for each call.

The another half being "guess the type yourself":
\begin{code}
  unpackâ‚€ : {A : _} â†’ Id A â†’ A
  unpackâ‚€ (pack a) = a
\end{code}
which has a special `âˆ€` syntax sugar:
\begin{code}
  -- input for âˆ€ is \all or \forall
  unpack : âˆ€ {A} â†’ Id A â†’ A
  unpack (pack a) = a

  -- explicit argument version:
  unpackâ‚ : âˆ€ A â†’ Id A â†’ A
  unpackâ‚ _ (pack a) = a
\end{code}

`âˆ€` extends to the right up to the first arrow:
\begin{code}
  unpackâ‚‚ : âˆ€ {A B} â†’ Id A â†’ Id B â†’ A
  unpackâ‚‚ (pack a) _ = a

  unpackâ‚ƒ : âˆ€ {A} (_ : Id A) {B} â†’ Id B â†’ A
  unpackâ‚ƒ (pack a) _ = a
\end{code}

Datatype syntax assumes implicit `âˆ€` when there is no type specified:
\begin{code}
  data ForAllId A (B : Id A) : Set where
\end{code}

It is important to note that Agda's `âˆ€` is quite different from Haskell's `âˆ€` (`forall`).
When we say `âˆ€ n` in Agda it's perfectly normal for `n : â„•` to be inferred, but in Haskell `âˆ€ n` always means `{n : Set}`, *[i.e. Haskell's `âˆ€` is an implicit (Hindley-Milner) version of second order universal quantifier while in Agda it's just a syntax sugar]*.

Syntax misinterpreting becomes a huge problem when working with more than one universe level (more on that below).
It is important to train yourself to desugar type expressions subconsciously (by doing in consciously at first).
It will save hours of your time later.
For instance, `âˆ€ {A} â†’ Id A â†’ A` means `{A : _} â†’ (_ : Id A) â†’ A` (where the last `â†’ A` should be interpreted as `â†’ (_ : A)`), i.e. the first `A` is a variable name, while the other expressions are types.

Finally, the last meaning of an underscore is to mark arguments' places in function names for the `MixFix` parser, i.e. an underscore in a function name marks the place where the arguments goes:
\begin{code}
  if_then_else_ : {A : Set} â†’ Bool â†’ A â†’ A â†’ A
  if true then a else _ = a
  if false then _ else b = b

  -- Are two â„•s equal?
  _=â„•?_ : â„• â†’ â„• â†’ Bool
  zero   =â„•? zero   = true
  zero   =â„•? succ m = false
  succ m =â„•? zero   = false
  succ n =â„•? succ m = n =â„•? m

  -- Sum for â„•.
  infix 6 _+_
  _+_ : â„• â†’ â„• â†’ â„•
  zero   + n = n
  succ n + m = succ (n + m)

  ifthenelseTestâ‚€ : â„•
  ifthenelseTestâ‚€ = if (zero + succ zero) =â„•? zero
    then zero
    else succ (succ zero)

  -- Lists
  data List (A : Set) : Set where
    []  : List A
    _âˆ·_ : A â†’ List A â†’ List A

  [_] : {A : Set} â†’ A â†’ List A
  [ a ] = a âˆ· []
  
  listTestâ‚ : List â„•
  listTestâ‚ = []

  listTestâ‚‚ : List â„•
  listTestâ‚‚ = zero âˆ· (zero âˆ· (succ zero âˆ· []))
\end{code}
Note the fixity declaration `infix` which has the same meaning as in Haskell.
We didn't write `infixl` for a reason.
With declared associativity Agda would not print redundant parentheses, which is good in general, but would somewhat complicate explanation of a several things below.

There is a `where` construct, just like in Haskell:
\begin{code}
  ifthenelseTestâ‚ : â„•
  ifthenelseTestâ‚ = if (zero + succ zero) =â„•? zero
    then zero
    else x
    where
    x = succ (succ zero)
\end{code}

While pattern matching, there is a special case when a type we are trying to pattern match on is obviously (*[type inhabitance problem is undecidable in a general case]*) empty.
This special case is called an "absurd pattern":
\begin{code}
  -- âŠ¥ implies anything.
  âŠ¥-elim : {A : Set} â†’ âŠ¥ â†’ A
  âŠ¥-elim ()
\end{code}
which allows you to skip a right-hand side of a definition.

You can bind variables like that still:
\begin{code}
  -- Absurd implies anything, take two.
  âŠ¥-elimâ‚€ : {A : Set} â†’ âŠ¥ â†’ A
  âŠ¥-elimâ‚€ x = âŠ¥-elim x
\end{code}

Agda has records, which work very much like `newtype` declarations in Haskell, i.e. they are datatypes with a single constructor that is not stored.

\begin{code}
  record Pair (A B : Set) : Set where
    field
      first  : A
      second : B

  getFirst : âˆ€ {A B} â†’ Pair A B â†’ A
  getFirst = Pair.first
\end{code}

Note, however, that to prevent name clashes record definition generates a module with field extractors inside.

There is a convention to define a type with one element as a record with no fields:
\begin{code}
  -- input for âŠ¤ is \top
  -- One element type. Record without fields. True proposition.
  record âŠ¤ : Set where

  tt : âŠ¤
  tt = record {}
\end{code}

A special thing about this convention is that an argument of an empty record type automatically gets the value `record {}` when applied implicitly or with underscore.

Lastly, Agda uses oversimplified lexer that splits tokens by spaces, parentheses, and braces.
For instance (note the name of the variable binding):
\begin{code}
  -- input for â€µ is \`
  -- input for â€² is \'
  âŠ¥-elimâ€µâ€² : {A : Set} â†’ âŠ¥ â†’ A
  âŠ¥-elimâ€µâ€² âˆ€x:âŠ¥â†’-- = âŠ¥-elim âˆ€x:âŠ¥â†’--
\end{code}
is totally fine. Also note that `--` doesn't generate a comment here.

### The magic of dependent types

Let's define the division by two:
\begin{code}
  div2 : â„• â†’ â„•
  div2 zero = zero
  div2 (succ (succ n)) = succ (div2 n)
\end{code}
the problem with this definition is that Agda is total and we have to extend this function for odd numbers
\begin{code}
  div2 (succ zero) = {!check me!}
\end{code}
by changing `{!check me!}` into some term, most common choice being `zero`.

Suppose now, we know that inputs to `div2` are always even and we don't want to extend `div2` for the `succ zero` case.
How do we constrain `div2` to even naturals only?
With a predicate! That is, `even` predicate:
\begin{code}
  even : â„• â†’ Set
  even zero = âŠ¤
  even (succ zero) = âŠ¥
  even (succ (succ n)) = even n
\end{code}
which returns `âŠ¤` with with a trivial proof `tt` when argument is even and empty `âŠ¥` then the argument is odd.

Now the definition of `div2e` constrained to even naturals only becomes:
\begin{code}
  div2e : (n : â„•) â†’ even n â†’ â„• -- Note, we have to give a name `n` to the first argument here
  div2e zero p = zero
  div2e (succ zero) ()
  div2e (succ (succ y)) p = succ (div2e y p) -- Note, a proof of `even (succ (succ n))` translates
                                             -- to a proof of `even n` by the definition of `even`.
\end{code}

When programming with dependent types, a predicate on `A` becomes a function from `A` to types, i.e. `A â†’ Set`.
If `a : A` satisfies the predicate `P : A â†’ Set` then the function `P` returns a type with each element being a proof of `P a`, in a case `a` doesn't satisfy `P` it returns an empty type.

The magic of dependent types makes the type of the second argument of `div2e` change every time we pattern match on the first argument `n`.
From the callee side, if the first argument is odd then the second argument would get `âŠ¥` type sometime (after a number of recursive calls) enabling the use of an absurd pattern.
From the caller side, we are not able to call the function with an odd `n`, since we have no means to construct a value for the second argument in this case.

### Type families and Unification

There is another way to define "even" predicate. This time with a datatype _indexed_ by â„•:
\begin{code}
  data Even : â„• â†’ Set where
    ezero  : Even zero
    e2succ : {n : â„•} â†’ Even n â†’ Even (succ (succ n))

  twoIsEven : Even (succ (succ zero))
  twoIsEven = e2succ ezero
\end{code}

`Even : â„• â†’ Set` is a family of types indexed by â„• and obeying the following rules:

* `Even zero` has one element `ezero`.
* For any given `n` type `Even (succ (succ n))` has one element if `Even n` is nonempty.
* There are no other elements.

Compare this to `even : â„• â†’ Set` definition translation:

* There is a trivial proof that `zero` has property `even`.
* There is no proof that `succ zero` has property `even`.
* If `n` has property `even` then so has `succ (succ n)`.

In other words, the difference is that `Even : â„• â†’ Set` _constructs_ a type whereas `even : â„• â†’ Set` _returns_ a type when applied to an element of `â„•`.

The proof that two is even `even (succ (succ zero))` literally says "two is even because it has a trivial proof", whereas the proof that two is even `twoIsEven` says "two is even because zero is even and two is the successor of the successor of zero".

`Even` datatype allows us to define another non-extended division by two for `â„•`:
\begin{code}
  div2E : (n : â„•) â†’ Even n â†’ â„•
  div2E zero ezero = zero
  div2E (succ zero) ()
  div2E (succ (succ n)) (e2succ stilleven) = succ (div2E n stilleven) -- Compare this case to div2e.
\end{code}
Note, there is no case for `div2E zero (e2succ x)` since `e2succ x` has the wrong type, there is no such constructor in `Even zero`.
For the `succ zero` case the type of the second argument is not `âŠ¥`, but is empty.
How do we know that?
Unification!

Unification is the most important (at least with pattern matching on inductive datatypes involved) and easily forgotten aspect of dependently typed programming.
Given two terms `M` and `N` unification tries to find a substitution `s` such that using `s` on `M` gives the same result as using `s` on `N`.
The precise algorithm definition is pretty long, but the idea is simple: to decide if two expressions could be unified we

* reduce them as much as possible,
* then traverse their spines until we
    * hit an obvious difference between them,
    * find a place where we can not decide for sure,
    * or successfully finish the traversal generating a substitution `s`.

For instance:

* To unify [`(succ a) + b` with `succ (c + d)`] we need reduce both of them, now we need to unify [`succ (a + b)` with `succ (c + d)`], which means that we need to unify [`a + b` with `c + d`], which means that we need to unify [`a` with `c`] and [`b` with `d`], which means that [`a = c`, `b = d`].
* On the other hand, `succ a` can not be unified with `zero` for any `a`, and `succ b` can not be unified with `b` for any `b`.
* We don't know if it's possible to unify `foo n` with `zero` for some unknown function `foo` (it might or might not reduce to `zero` for some `n`).
    
In the code above `succ zero` doesn't unify with any of the `Even` constructors' indexes [`zero`, `succ (succ n)`] which makes this type obviously empty by its definition.

*[Refer to "The view from the left" paper by McBride and McKinna [@McBride-McKinna:the-view-from-the-left] for more details on pattern matching with type families.]*

### More type families and less Unification

In datatype declarations things before a `:` are called "parameters", things after the colon but before a `Set` are called "indexes".

There is a famous datatype involving both of them:
\begin{code}
  data Vec (A : Set) : â„• â†’ Set where
    []  : Vec A zero
    _âˆ·_ : âˆ€ {n} â†’ A â†’ Vec A n â†’ Vec A (succ n)
\end{code}

`Vec A n` is a vector of values of type `A` and length `n`, `Vec` has a parameter of type `Set` and is indexed by values of type `â„•`.
Compare this definition to the definition of `List` and `Even`.
Note also, that Agda tolerates different datatypes with constructors of the same name (see below for how this is resolved).

We can not omit the clause for an `[]` case in a function which takes a head of a `List`:
\begin{code}
  headâ‚€ : âˆ€ {A} â†’ List A â†’ A
  headâ‚€ []       = {!check me!}
  headâ‚€ (a âˆ· as) = a
\end{code}
but we have nothing to write in place of `{!check me!}` there (if we want to be total).

On the other hand, there is no `[]` constructor in a `Vec A (succ n)` type:
\begin{code}
  head : âˆ€ {A n} â†’ Vec A (succ n) â†’ A
  head (a âˆ· as) = a
\end{code}
Note that there are no absurd patterns here, `Vec A (succ n)` is inhabited, it just happens that there is no `[]` in there.

By the way, the `Vec` type is famous for a concatenation function:
\begin{code}
  -- Concatenation for `List`s
  _++_ : âˆ€ {A} â†’ List A â†’ List A â†’ List A
  []       ++ bs = bs
  (a âˆ· as) ++ bs = a âˆ· (as ++ bs)

  -- Concatenation for `Vec`tors
  -- The length of a concatenation is the sum of lengths of arguments and is available in types.
  _++v_ : âˆ€ {A n m} â†’ Vec A n â†’ Vec A m â†’ Vec A (n + m)
  []       ++v bs = bs
  (a âˆ· as) ++v bs = a âˆ· (as ++v bs)
\end{code}
Compare `_+_`, `_++_`, and `_++v_` definitions.

Why does the definition of `_++v_` work?
Because we defined `_+_` this way!
In the first clause of `_++v_` the type of `[]` gives `n = zero` by unification, `zero + m = m` by the `_+_` definition, `bs : Vec A m`.
Similarly, in the second clause `n = succ n0`, `as : Vec A n0`, `(succ n0) + m = succ (n0 + m)` by the `_+_` definition, `a âˆ· (as ++ bs) : succ (n0 + m)`.

### Dotted patterns and Unification

Let's define a substraction:
\begin{code}
  infix 6 _-_
  _-_ : â„• â†’ â„• â†’ â„•
  zero   - _      = zero
  succ n - zero   = succ n
  succ n - succ m = n - m
\end{code}
Note that `n - m = zero` for `m > n`.

Let us get rid of this `(succ n) - zero` case with `_â‰¤_` relation:
\begin{code}
  data _â‰¤_ : â„• â†’ â„• â†’ Set where
    zâ‰¤n : âˆ€ {n}           â†’ zero â‰¤ n
    sâ‰¤s : âˆ€ {n m} â†’ n â‰¤ m â†’ succ n â‰¤ succ m
\end{code}

We are now able to write a substraction that is not extended for `m > n`.
\begin{code}
  subâ‚€ : (n m : â„•) â†’ m â‰¤ n â†’ â„•
  subâ‚€ n zero (zâ‰¤n .{n}) = n
  subâ‚€ .(succ n) .(succ m) (sâ‰¤s {m} {n} y) = subâ‚€ n m y
\end{code}

Note the dots, these are called "dotted patterns".
Ignore them for a second.

Consider the case
`subâ‚€ n zero (zâ‰¤n {k})`.
The type of the third argument is `zero â‰¤ n`.
The type of `zâ‰¤n {k}` is `zero â‰¤ k`.
Unification of these two types gives [`k = n`, `m = zero`].
After a substitution we get
`subâ‚€ n zero (zâ‰¤n {n})`.
Which of the `n`s we want to bind/match on?
In the code above we say "on the first" and place a dot before the second occurrence to mark this intention.
Dotted pattern says "do not match on this, it is the only possible value" to the compiler.

The second clause is
`subâ‚€ n m (sâ‰¤s {n'} {m'} y)`.
The type of the third argument is `m â‰¤ n`.
The type of `sâ‰¤s {n'} {m'} y` is `succ n' â‰¤ succ m'`.
This gives [`n = succ n'`, `m = succ m'`].
This time we decided to match on `n'` and `m'`.

Rewritten with a `case` construct from Haskell (Agda doesn't have `case`, see below) the code above becomes (in pseudo-Haskell):
\begin{spec}
  subâ‚€ n m even = case even of
    zâ‰¤n {k}     -> case m of -- [`k = n`, `m = zero`]
      zero    -> n
      succ m' -> __IMPOSSIBLE__  -- since `m = zero` doesn't merge with `m = succ m'`
    sâ‰¤s n' m' y -> subâ‚€ n' m' y  -- [`n = succ n'`, `m = succ n'`]
\end{spec}

Where `__IMPOSSIBLE__` is just like an `undefined` but is never executed.

Note, that we have [`k = n`, `m = zero`] in the first case for even.
This means we can dot the first usage of `zero` to optimize the match on `m` away: 
\begin{code}
  subâ‚ : (n m : â„•) â†’ m â‰¤ n â†’ â„•
  subâ‚ n .zero (zâ‰¤n .{n}) = n
  subâ‚ .(succ n) .(succ m) (sâ‰¤s {m} {n} y) = subâ‚ n m y
\end{code}
which translates to
\begin{spec}
subâ‚ n m even = case even of
  zâ‰¤n {k}     -> n
  sâ‰¤s n' m' y -> subâ‚ n' m' y
\end{spec}

Finally, we can also rewrite `sub` to match on the first two arguments (usual, common sense definition):
\begin{code}
  sub : (n m : â„•) â†’ m â‰¤ n â†’ â„•
  sub n zero (zâ‰¤n .{n}) = n
  sub (succ n) (succ m) (sâ‰¤s .{m} .{n} y) = sub n m y
\end{code}
which translates into the following:
\begin{spec}
  sub n m even = case m of
    zero   -> case even of
        zâ‰¤n {k}       -> n
        sâ‰¤s {k} {l} y -> __IMPOSSIBLE__ -- since `zero` (`m`) can't be unified
                                        -- with `succ k`
    succ m' -> case n of
      zero   -> case even of
        zâ‰¤n {k}       -> __IMPOSSIBLE__ -- since `succ m'` (`m`) can't be unified
                                        -- with `zero`
        sâ‰¤s {k} {l} y -> __IMPOSSIBLE__ -- since `zero` (`n`) can't be unified
                                        -- with `succ l`
      succ n' -> case even of
        zâ‰¤n {k}       -> __IMPOSSIBLE__ -- since `succ n'` (`n`) can't be unified
                                        -- with `zero`
        sâ‰¤s {k} {l} y -> sub n' m' y
\end{spec}

**Exercise.** Write out the unification constraints for the pseudo-Haskell translation above.

Note, that `sub n m p` computes the difference between `n` and `m` while `subâ‚€` and `subâ‚` extract it from the proof `p`.
Note also, that for `sub n zero` the third argument is always `zâ‰¤n {n}`, so we would like to write
\begin{spec}
  subâ‚‚ : (n m : â„•) â†’ m â‰¤ n â†’ â„•
  subâ‚‚ n zero .(zâ‰¤n {n}) = n
  subâ‚‚ (succ n) (succ m) (sâ‰¤s .{m} .{n} y) = subâ‚‚ n m y
\end{spec}
but Agda doesn't allow this. See below for why.

We can write
\begin{code}
  subâ‚ƒ : (n m : â„•) â†’ m â‰¤ n â†’ â„•
  subâ‚ƒ n zero _ = n
  subâ‚ƒ (succ n) (succ m) (sâ‰¤s .{m} .{n} y) = subâ‚ƒ n m y
\end{code}
still.

**Exercise.** Translate the following definition into pseudo-Haskell with unification constraints:
\begin{code}
  subâ‚„ : (n m : â„•) â†’ m â‰¤ n â†’ â„•
  subâ‚„ n zero (zâ‰¤n .{n}) = n
  subâ‚„ (succ .n) (succ .m) (sâ‰¤s {m} {n} y) = subâ‚„ n m y
\end{code}

The moral is that **dotted patterns are inlined unification constraints**.
This is why we couldn't dot `zâ‰¤n {n}` in the first clause of `subâ‚‚`, Agda didn't generate such a constraint (it could, have it tried a bit harder).

### Propositional equality and Unification

We shall now define the most useful type family, that is, Martin-LÃ¶f's equivalence (values only version, though):
\begin{code}
  -- â‰¡ is \==
  infix 4 _â‰¡_
  data _â‰¡_ {A : Set} (x : A) : A â†’ Set where
    refl : x â‰¡ x
\end{code}

For `x y : A` the type `x â‰¡ y` has exactly one constructor `refl` if `x` and `y` are _convertible_, i.e. there exist such `z` that `z â†’Î²âœ´ x` and `z â†’Î²âœ´ y`, where `â†’Î²âœ´` is "Î²-reduces in zero or more steps".
By a consequence from a Church-Rosser theorem and strong normalization convertibility can be solved by normalization.
Which means that unification will both check convertibility and fill in any missing parts.
In other words, `x y : A` the type `x â‰¡ y` has exactly one constructor `refl` if `x` and `y` unify with each other.

Let's prove some of `_â‰¡_`'s properties:
\begin{code}
  -- _â‰¡_ is symmetric
  sym : {A : Set} {a b : A} â†’ a â‰¡ b â†’ b â‰¡ a
  sym refl = refl

  -- transitive
  trans : {A : Set}{a b c : A} â†’ a â‰¡ b â†’ b â‰¡ c â†’ a â‰¡ c
  trans refl refl = refl

  -- and congruent
  cong : {A B : Set} {a b : A} â†’ (f : A â†’ B) â†’ a â‰¡ b â†’ f a â‰¡ f b
  cong f refl = refl
\end{code}

Consider the case `sym {A} {a} {b} (refl {x = a})`.
Matching on `refl` gives [`b = a`] equation, i.e. the clause actually is `sym {A} {a} .{a} (refl {x = a})` which allows to write `refl` on the right-hand side.
Other proofs are similar.

Note, we can prove `sym` the other way:
\begin{code}
  symâ€² : {A : Set}{a b : A} â†’ a â‰¡ b â†’ b â‰¡ a
  symâ€² {A} .{b} {b} refl = refl
\end{code}

`sym` packs `a` into `refl`. `symâ€²` packs `b`. "Are these two definitions equal?" is an interesting philosophical question.
(From the Agda's point of view they are.)

Since dotted patterns are just unification constraints, you don't have to dot implicit arguments when you don't bind or match on them.

`_â‰¡_` type family is called "propositional equality".
In Agda's standard library it has a bit more general definition, see below.

### Proving things interactively

With `_â‰¡_` we can finally prove something from basic number theory.
Let's do this interactively.

Our first victim is the associativity of `_+_`.
\begin{code}
  +-assocâ‚€ : âˆ€ a b c â†’ (a + b) + c â‰¡ a + (b + c)
  +-assocâ‚€ a b c = {!!}
\end{code}

Note a mark `{!!}`.
Anything of the form `{!expr!}` with `expr` being any string (including empty) a _goal_ after a buffer is loaded by agda2-mode.
Typing `{!!}` is quite tedious, so there is a shortcut `?`.
All `?` symbols are automatically transformed into `{!!}` when a buffer is loaded.

Goals appear as green holes in a buffer, pressing special key sequences while in a goal allows to ask Agda questions about and perform actions on a code.
In this document "check me" in a goal means that this goal is not expected to be filled, it's just an example.

Press `C-c C-l` (load) to load and typecheck the buffer.

Placing the cursor in the goal above (the green hole in the text) and pressing `C-c C-c a RET` (case by `a`) gives (ignore changes to the name of a function and "check me"s everywhere):
\begin{code}
  +-assocâ‚ : âˆ€ a b c â†’ (a + b) + c â‰¡ a + (b + c)
  +-assocâ‚ zero b c = {!check me!}
  +-assocâ‚ (succ a) b c = {!check me!}
\end{code}
Press `C-c C-,` (goal type and context) while in the goal.
This will show the goal type and the context inside the hole.
Write `refl` in there and press `C-c C-r` (refine), this gives:
\begin{code}
  +-assocâ‚‚ : âˆ€ a b c â†’ (a + b) + c â‰¡ a + (b + c)
  +-assocâ‚‚ zero b c = refl
  +-assocâ‚‚ (succ a) b c = {!check me!}
\end{code}
`C-c C-f` (next goal), write `cong succ` there, `C-c C-r`:
\begin{code}
  +-assocâ‚ƒ : âˆ€ a b c â†’ (a + b) + c â‰¡ a + (b + c)
  +-assocâ‚ƒ zero b c = refl
  +-assocâ‚ƒ (succ a) b c = cong succ {!check me!}
\end{code}
Next goal, goal type and context, press `C-c C-a` (auto proof search):
\begin{code}
  +-assoc : âˆ€ a b c â†’ (a + b) + c â‰¡ a + (b + c)
  +-assoc zero b c = refl
  +-assoc (succ a) b c = cong succ (+-assoc a b c)
\end{code}
Done.

(In Agda 2.3.2 you have to reload a buffer for proof search to work, it's probably a bug.)

Similarly, we prove
\begin{code}
  lemma-+zero : âˆ€ a â†’ a + zero â‰¡ a
  lemma-+zero zero = refl
  lemma-+zero (succ a) = cong succ (lemma-+zero a)

  lemma-+succ : âˆ€ a b â†’ succ a + b â‰¡ a + succ b
  lemma-+succ zero b = refl
  lemma-+succ (succ a) b = cong succ (lemma-+succ a b)
\end{code}

The commutativity for `_+_` is not hard to follow too:
\begin{code}
  -- A fun way to write transitivity
  infixr 5 _~_
  _~_ = trans

  +-comm : âˆ€ a b â†’ a + b â‰¡ b + a
  +-comm zero b = sym (lemma-+zero b)
  +-comm (succ a) b = cong succ (+-comm a b) ~ lemma-+succ b a
\end{code}

Nice way to "step" through a proof is to wrap some subexpression with `{! !}`, e.g.:
\begin{spec}
  +-comm (succ a) b = cong succ {!(+-comm a b)!} ~ lemma-+succ b a
\end{spec}
and ask for a type, context and inferred type of a goal with `C-c C-l` followed by `C-c C-.`, refine, wrap another subexpression, repeat.
I dream of a better interface for this.

### Solving type equations

The second case of `+-comm` is pretty fun example to infer implicit arguments by hand. Let's do that.
Algorithm is as follows:

* First, expand all implicit arguments and explicit arguments applied with `_` in a term into "metavariables", that is, special meta-level variables not bound anywhere in the program.
* Look at the types of all symbols and construct a system of equations.
For instance, if you see `term1 term2 : D`, `term1 : A â†’ B` and `term2 : C`, add equations `A == C` and `B == D` to the system.
* Solve the system with a help from unification. Two possible results:
    * All the metavariables got their values from the solution. Success.
    * There are some that didn't. This situation is reported to a user as "unsolved metas" type checking result.
      These act like warnings while you are not trying to compile or to type check in a "safe mode".
      In the latter two cases unsolved metas transform into errors.
* Substitute the values of metavariables back into the term.

Applying the first step of the algorithm to a term
\begin{spec}
trans (cong succ (+-comm1 a b)) (lemma-+succ b a)
\end{spec}
gives:
\begin{spec}
trans {ma} {mb} {mc} {md} (cong {me} {mf} {mg} {mh} succ (+-comm a b)) (lemma-+succ b a)
\end{spec}
with `m*` being metavariables.

`a b : â„•` since `_+_ : â„• â†’ â„• â†’ â„•` in the type of `+comm`.
This gives the following system (with duplicated equations and metavariable applications skipped):
\begin{spec}
trans (cong succ (+-comm a b)) (lemma-+succ b a) : _â‰¡_ {â„•} (succ a + b) (b + succ a)
trans (cong succ (+-comm a b)) (lemma-+succ b a) : _â‰¡_ {â„•} (succ (a + b)) (b + succ a) -- after normalization
ma = â„•
mb = succ (a + b)
md = b + succ a
+-comm a b : _â‰¡_ {â„•} (a + b) (b + a)
mg = (a + b)
me = â„•
mh = (b + a)
mf = â„•
cong succ (+-comm a b) : _â‰¡_ {â„•} (succ (a + b)) (succ (b + a))
mc = succ (b + a)
lemma-+succ b a : _â‰¡_ {â„•} (succ b + a) (b + succ a)
lemma-+succ b a : _â‰¡_ {â„•} (succ (b + a)) (b + succ a) -- after normalization
trans (cong succ (+-comm a b)) (lemma-+succ b a) : _â‰¡_ {â„•} (succ a + b) (b + succ a)
\end{spec}

The most awesome thing about this is that from Agda's point of view, a goal is just a metavariable of a special kind.
When you ask for a type of a goal with `C-c C-t` or `C-c C-,` Agda prints everything it has for the corresponding metavariable.
Funny things like `?0`, `?1`, and etc in agda2-mode outputs are references to these metavariables.
For instance, in the following:
\begin{code}
  metaVarTest : Vec â„• (div2 (succ zero)) â†’ â„•
  metaVarTest = {!check me!}
\end{code}
the type of the goal mentions the name of very first goal metavariable from this article.

By the way, to resolve datatype constructor overloading Agda infers the type for a constructor call expected at the call site, and unifies the inferred type with the types of all possible constructors of the same name.
If there are no matches found, an error is reported.
In case with more than one alternative available, an unsolved meta (for the return type metavariable) is produced.

### Termination checking, well-founded induction

Work in progress.

### Propositional equality exercises

**Exercise.** Define multiplication by induction on the first argument:
\begin{code}
  module Exercise where
    infix 7 _*_
    _*_ : â„• â†’ â„• â†’ â„•
    n * m = {!!}
\end{code}
so that the following proof works:
\begin{code}
    -- Distributivity.
    *+-dist : âˆ€ a b c â†’ (a + b) * c â‰¡ a * c + b * c
    *+-dist zero b c = refl
    -- Î» is \lambda
    *+-dist (succ a) b c = cong (Î» x â†’ c + x) (*+-dist a b c) ~ sym (+-assoc c (a * c) (b * c))
\end{code}

Now, fill in the following goals:
\begin{code}
    *-assoc : âˆ€ a b c â†’ (a * b) * c â‰¡ a * (b * c)
    *-assoc zero b c = refl
    *-assoc (succ a) b c = *+-dist b (a * b) c ~ cong {!!} (*-assoc a b c)

    lemma-*zero : âˆ€ a â†’ a * zero â‰¡ zero
    lemma-*zero a = {!!}

    lemma-+swap : âˆ€ a b c â†’ a + (b + c) â‰¡ b + (a + c)
    lemma-+swap a b c = sym (+-assoc a b c) ~ {!!} ~ +-assoc b a c

    lemma-*succ : âˆ€ a b â†’ a + a * b â‰¡ a * succ b 
    lemma-*succ a b = {!!}

    *-comm : âˆ€ a b â†’ a * b â‰¡ b * a
    *-comm a b = {!!}
\end{code}
Pressing `C-c C-.` while there is a term in a hole shows a goal type, context and the term's inferred type.
Incredibly useful key sequence for interactive proof editing.

### Pattern matching with `with`

Consider the following implementation of a `filter` function in Haskell:
\begin{spec}
  filter :: (a â†’ Bool) â†’ [a] â†’ [a]
  filter p [] = []
  filter p (a : as) = case p a of
    True  -> a : (filter p as)
    False -> filter p as
\end{spec}

It could be rewritten into Agda like this:
\begin{code}
  filter : {A : Set} â†’ (A â†’ Bool) â†’ List A â†’ List A
  filter p [] = []
  filter p (a âˆ· as) with p a
  ... | true  = a âˆ· (filter p as)
  ... | false = filter p as
\end{code}
which doesn't look very different.
But desugaring `...` by the rules of Agda syntax makes it a bit less similar: 
\begin{code}
  filterâ‚€ : {A : Set} â†’ (A â†’ Bool) â†’ List A â†’ List A
  filterâ‚€ p [] = []
  filterâ‚€ p (a âˆ· as) with p a
  filterâ‚€ p (a âˆ· as) | true  = a âˆ· (filterâ‚€ p as)
  filterâ‚€ p (a âˆ· as) | false = filterâ‚€ p as
\end{code}

There's no direct analogue to `case` in Agda, `with` construction allows pattern matching on intermediate expressions (just like Haskell's `case`), but (unlike `case`) on a top level only.
Thus `with` effectively just adds a "derived" argument to a function.
Just like with normal arguments, pattern matching on a derived argument might change some types in a context.

The top level restriction simplifies all the dependently typed stuff (mainly related to dotted patterns), but makes some things a little bit more awkward (in most cases you can emulate `case` with a subterm placed into a `where` block).
Syntactically, vertical bars separate normal arguments from a derived ones and a derived ones from each other.

Obfuscating the function above gives:
\begin{code}
  filterN : {A : Set} â†’ (A â†’ Bool) â†’ List A â†’ List A
  filterN p [] = []
  filterN p (a âˆ· as) with p a
  filterN p (a âˆ· as) | true  with as
  filterN p (a âˆ· as) | true | [] = a âˆ· []
  filterN p (a âˆ· as) | true | b âˆ· bs with p b
  filterN p (a âˆ· as) | true | b âˆ· bs | true  = a âˆ· (b âˆ· filterN p bs)
  filterN p (a âˆ· as) | true | b âˆ· bs | false = a âˆ· filterN p bs
  filterN p (a âˆ· as) | false = filterN p as
  -- or alternatively
  filterP : {A : Set} â†’ (A â†’ Bool) â†’ List A â†’ List A
  filterP p [] = []
  filterP p (a âˆ· []) with p a
  filterP p (a âˆ· []) | true = a âˆ· []
  filterP p (a âˆ· []) | false = []
  filterP p (a âˆ· (b âˆ· bs)) with p a | p b
  filterP p (a âˆ· (b âˆ· bs)) | true  | true  = a âˆ· (b âˆ· filterP p bs)
  filterP p (a âˆ· (b âˆ· bs)) | true  | false = a âˆ· filterP p bs
  filterP p (a âˆ· (b âˆ· bs)) | false | true  = b âˆ· filterP p bs
  filterP p (a âˆ· (b âˆ· bs)) | false | false = filterP p bs
\end{code}
which shows that `with` could be nested and multiple matches are allowed to be done in parallel.

Let us prove that all these functions produce equal results when applied to equal arguments:
\begin{code}
  filterâ‰¡filterNâ‚€ : {A : Set} â†’ (p : A â†’ Bool) â†’ (as : List A) â†’ filter p as â‰¡ filterN p as
  filterâ‰¡filterNâ‚€ p [] = refl
  filterâ‰¡filterNâ‚€ p (a âˆ· as) = {!check me!}
\end{code}
note the goal type `(filter p (a âˆ· as) | p a) â‰¡ (filterN p (a âˆ· as) | p a)` which shows `p a` as derived argument to `filter` function.

Remember that to reduce `a + b` we had to match on `a` in the proofs above, matching on `b` gave nothing interesting because `_+_` was defined by induction on the first argument.
Similarly, to finish the `filterâ‰¡filterN` proof we have to match on `p a`, `as`, and `p b`, essentially duplicating the form of `filterN` term:
\begin{code}
  filterâ‰¡filterN : {A : Set} â†’ (p : A â†’ Bool) â†’ (as : List A) â†’ filter p as â‰¡ filterN p as
  filterâ‰¡filterN p [] = refl
  filterâ‰¡filterN p (a âˆ· as) with p a
  filterâ‰¡filterN p (a âˆ· as) | true with as
  filterâ‰¡filterN p (a âˆ· as) | true | [] = refl
  filterâ‰¡filterN p (a âˆ· as) | true | b âˆ· bs with p b
  filterâ‰¡filterN p (a âˆ· as) | true | b âˆ· bs | true = cong (Î» x â†’ a âˆ· (b âˆ· x)) (filterâ‰¡filterN p bs)
  filterâ‰¡filterN p (a âˆ· as) | true | b âˆ· bs | false = cong (_âˆ·_ a) (filterâ‰¡filterN p bs)
  filterâ‰¡filterN p (a âˆ· as) | false = filterâ‰¡filterN p as
\end{code}

***Exercise.*** Guess the types for `filterâ‰¡filterP` and `filterNâ‰¡filterP`. Argue which of these is easier to prove? Do it (and get the other one almost for free by transitivity).

### Rewriting with `with` and Unification

When playing with the proofs about filters you might had noticed that `with` does something interesting with a goal.

In the following hole
\begin{code}
  filterâ‰¡filterNâ‚ : {A : Set} â†’ (p : A â†’ Bool) â†’ (as : List A) â†’ filter p as â‰¡ filterN p as
  filterâ‰¡filterNâ‚ p [] = refl
  filterâ‰¡filterNâ‚ p (a âˆ· as) = {!check me!}
\end{code}
the type of the goal is `(filter p (a âˆ· as) | p a) â‰¡ (filterN p (a âˆ· as) | p a)`.
But after the following `with`
\begin{code}
  filterâ‰¡filterNâ‚‚ : {A : Set} â†’ (p : A â†’ Bool) â†’ (as : List A) â†’ filter p as â‰¡ filterN p as
  filterâ‰¡filterNâ‚‚ p [] = refl
  filterâ‰¡filterNâ‚‚ p (a âˆ· as) with p a | as
  ... | r | rs = {!check me!}
\end{code}
it becomes `(filter p (a âˆ· rs) | r) â‰¡ (filterN p (a âˆ· rs) | r)`.

Same things might happen not only to a goal but to a context as a whole:
\begin{code}
  strange-id : {A : Set} {B : A â†’ Set} â†’ (a : A) â†’ (b : B a) â†’ B a
  strange-id {A} {B} a ba with B a
  ... | r = {!check me!}
\end{code}
in the hole, both the type of `ba` and the goal's type are `r`.

From these observations we conclude that `with expr` creates a new variable, say `w`, and "backwards-substitutes" `expr` to `w` in a context, changing all the occurrences of `expr` the _types_ of the context to `w`.
Which means that in a resulting context every type that had `expr` as a subterm starts dependending on `w`.

This property allows using `with` for _rewriting_:
\begin{code}
  lemma-+zeroâ€² : âˆ€ a â†’ a + zero â‰¡ a
  lemma-+zeroâ€² zero = refl
  lemma-+zeroâ€² (succ a) with a + zero | lemma-+zeroâ€² a
  lemma-+zeroâ€² (succ a) | ._ | refl = refl

  -- same expression with expanded underscore:
  lemma-+zeroâ€²â‚€ : âˆ€ a â†’ a + zero â‰¡ a
  lemma-+zeroâ€²â‚€ zero = refl
  lemma-+zeroâ€²â‚€ (succ a) with a + zero | lemma-+zeroâ€²â‚€ a
  lemma-+zeroâ€²â‚€ (succ a) | .a | refl = refl
\end{code}

In these terms `a + zero` is replaced by a new variable, say `w`, which gives `lemma-+zeroâ€µ a : a â‰¡ w`.
Pattern matching on `refl` gives [`w = a`] and so the dotted pattern appears.
After that the goal type becomes `a â‰¡ a`.

This pattern
\begin{spec}
f ps with a | eqn
... | ._ | refl = rhs
\end{spec}
is so common that it has [its own short hand](https://lists.chalmers.se/pipermail/agda/2009/001513.html):
\begin{spec}
f ps rewrite eqn = rhs
\end{spec}

***Exercise.*** Prove (on paper) that rewriting a goal type with `with` and propositional equality is a syntax sugar for expressions built from `refl`, `sym`, `trans` and `cong`.

### Universes and postulates

When moving from Haskell to Agda expression "every type is of kind `*`, i.e. for any type `X`, `X : *`" transforms into "every _ground_ type is of type `Set`, i.e. for any ground type `X`, `X : Set`".
If we are willing to be consistent, we can't afford `Set : Set` because it leads to a number of paradoxes (more on them below).
Still, we might want to construct things like "a list of types" and our current implementation of `List` can not express this.

To solve this problem Agda introduces an infinite tower of `Set`s, i.e. `Set0 : Set1`, `Set1 : Set2`, and so on with `Set` being an alias for `Set0`.
Agda is also a predicative system which means that `Set0 â†’ Set0 : Set1`, `Set0 â†’ Set1 : Set2`, and so on, but not `Set0 â†’ Set1 : Set1`.
Note, however, that this tower is not cumulative, e.g. `Set0 : Set2` and `Set0 â†’ Set1 : Set3` are false typing judgments.

*[As far as I know, in theory nothing prevents us from making the tower cumulative, it's just so happened that Agda selected this route and not another. Predicativity is a much more subtle matter (more on that below).]*

A list of types now becomes:
\begin{code}
  data List1 (A : Set1) : Set1 where
    []  : List1 A
    _âˆ·_ : A â†’ List1 A â†’ List1 A
\end{code}
which looks very much like the usual `List` definition.

To prevent a code duplication like that Agda allows _universe polymorphic_ definitions.
To define the type `Level` of _universe levels_ we need a bit of _postulate_ magic:
\begin{spec}
  postulate Level : Set
  postulate lzero : Level
  postulate lsucc : Level â†’ Level
  postulate _âŠ”_   : Level â†’ Level â†’ Level
\end{spec}

Postulates essentially define propositions without proofs, i.e. they say "trust me, I know this to be true".
Obviously, this can be exploited to infer contradictions:
\begin{code}
  postulate undefined : {A : Set} â†’ A
\end{code}
but for every postulate Agda expects to be safe there is a `BUILTIN` pragma that checks the postulated definition promoting it from a simple postulate to an axiom. For `Level` there are the following `BUILTIN`s:
\begin{spec}
  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lzero #-}
  {-# BUILTIN LEVELSUC  lsucc #-}
  {-# BUILTIN LEVELMAX  _âŠ”_   #-}
\end{spec}

The `Level` type works very much like `â„•`.
It has two constructors `lzero` and `lsucc` that signify zero and successor, there is also an operator `_âŠ”_` which returns a maximum from its arguments.
The difference between `â„•` and `Level` is that we are not allowed to pattern match on elements of the latter.

Given the definition above, expression `Set Î±` for `Î± : Level` means "the `Set` of level `Î±`".

We are now able to define universe polymorphic list in the following way:
\begin{spec}
  data PListâ‚€ {Î± : Level} (A : Set Î±) : Set Î± where
    []  : PListâ‚€ A
    _âˆ·_ : A â†’ PListâ‚€ A â†’ PListâ‚€ A
  -- or a bit nicer:
  data PListâ‚ {Î±} (A : Set Î±) : Set Î± where
    []  : PListâ‚ A
    _âˆ·_ : A â†’ PListâ‚ A â†’ PListâ‚ A
\end{spec}

It is interesting to note that Agda could have gone another route, say "GHC route", by defining all the builtin things inside with fixed names.
Instead, `BUILTIN` pragma allows us to redefine the names of the builtins, which is very helpful when we want to write our own standard library.
This is exactly what we are now going to do.

## Library

### Modules and the end of throw away code

Note that we have been writing everything above inside a module called `ThrowAwayIntroduction`.
From here on we are going to (mostly) forget about it and write a small standard library for Agda from scratch.
The idea is to remove any module with a name prefixed by "ThrowAway" from this file to produce the library code.
To make the implementation of this idea as simple as possible we place markers like:
\begin{code}
{- end of ThrowAwayIntroduction -}
\end{code}
at the ends of throw away code.
It allows to generate the library by a simple shell command:

    cat BrutalDepTypes.lagda | sed '/^\\begin{code}/,/^\\end{code}/ ! d; /^\\begin{code}/ d; /^\\end{code}/ c \
    ' | sed '/^ *module ThrowAway/,/^ *.- end of ThrowAway/ d;'

We are now going to redefine everything useful from above in a universe polymorphic way (when applicable), starting with `Level`s:
\begin{code}
module Level where
  -- Universe levels
  postulate Level : Set
  postulate lzero : Level
  postulate lsucc : Level â†’ Level
  -- input for âŠ” is \sqcup
  postulate _âŠ”_   : Level â†’ Level â†’ Level

  infixl 5 _âŠ”_
  
  -- Make them work
  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lzero #-}
  {-# BUILTIN LEVELSUC  lsucc #-}
  {-# BUILTIN LEVELMAX  _âŠ”_   #-}
\end{code}

Each module in Agda has an export list.
Everything defined in a module gets appended to it.
To place things defined for export in another module into a current context there is an `open` construct:
\begin{spec}
open ModuleName
\end{spec}
This doesn't append `ModuleName`'s export list to current module's export list.
To do that we need to add `public` keyword at the end:
\begin{code}
open Level public
\end{code}

### Common functions with types not for the faint of heart

**Exercise.** Understand what is going on in types of the following functions:
\begin{code}
module Function where
  -- Dependent application
  infixl 0 _$_
  _$_ : âˆ€ {Î± Î²}
      â†’ {A : Set Î±} {B : A â†’ Set Î²}
      â†’ (f : (x : A) â†’ B x)
      â†’ ((x : A) â†’ B x)
  f $ x = f x
  
  -- Simple application
  infixl 0 _$â€²_
  _$â€²_ : âˆ€ {Î± Î²}
      â†’ {A : Set Î±} {B : Set Î²}
      â†’ (A â†’ B) â†’ (A â†’ B)
  f $â€² x = f $ x

  -- input for âˆ˜ is \o
  -- Dependent composition
  _âˆ˜_ : âˆ€ {Î± Î² Î³}
      â†’ {A : Set Î±} {B : A â†’ Set Î²} {C : {x : A} â†’ B x â†’ Set Î³}
      â†’ (f : {x : A} â†’ (y : B x) â†’ C y)
      â†’ (g : (x : A) â†’ B x)
      â†’ ((x : A) â†’ C (g x))
  f âˆ˜ g = Î» x â†’ f (g x)
  
  -- Simple composition
  _âˆ˜â€²_ : âˆ€ {Î± Î² Î³}
      â†’ {A : Set Î±} {B : Set Î²} {C : Set Î³}
      â†’ (B â†’ C) â†’ (A â†’ B) â†’ (A â†’ C)
  f âˆ˜â€² g = f âˆ˜ g
  
  -- Flip
  flip : âˆ€ {Î± Î² Î³}
       â†’ {A : Set Î±} {B : Set Î²} {C : A â†’ B â†’ Set Î³} 
       â†’ ((x : A) â†’ (y : B) â†’ C x y)
       â†’ ((y : B) â†’ (x : A) â†’ C x y)
  flip f x y = f y x
  
  -- Identity
  id : âˆ€ {Î±} {A : Set Î±} â†’ A â†’ A
  id x = x
  
  -- Constant function
  const : âˆ€ {Î± Î²}
       â†’ {A : Set Î±} {B : Set Î²}
       â†’ (A â†’ B â†’ A)
  const x y = x

open Function public
\end{code}
Especially note the scopes of variable bindings in types.

### Logic

Intuitionistic `Logic` module:
\begin{code}
module Logic where
  -- input for âŠ¥ is \bot
  -- False proposition
  data âŠ¥ : Set where

  -- input for âŠ¤ is \top
  -- True proposition
  record âŠ¤ : Set where
 
  -- âŠ¥ implies anything at any universe level
  âŠ¥-elim : âˆ€ {Î±} {A : Set Î±} â†’ âŠ¥ â†’ A
  âŠ¥-elim ()
\end{code}

Propositional negation is defined as follows:
\begin{code}
  -- input for Â¬ is \lnot
  Â¬ : âˆ€ {Î±} â†’ Set Î± â†’ Set Î±
  Â¬ P = P â†’ âŠ¥
\end{code} 

The technical part of the idea of this definition is that the principle of explosion ("from a contradiction, anything follows") gets a pretty straightforward proof.

**Exercise.** Prove the following propositions:
\begin{code}
  module ThrowAwayExercise where
    contradiction : âˆ€ {Î± Î²} {A : Set Î±} {B : Set Î²} â†’ A â†’ Â¬ A â†’ B
    contradiction = {!!}
   
    contraposition : âˆ€ {Î± Î²} {A : Set Î±} {B : Set Î²} â†’ (A â†’ B) â†’ (Â¬ B â†’ Â¬ A)
    contraposition = {!!}

    contrapositionÂ¬ : âˆ€ {Î± Î²} {A : Set Î±} {B : Set Î²} â†’ (A â†’ Â¬ B) â†’ (B â†’ Â¬ A)
    contrapositionÂ¬ = {!!}

    â†’Â¬Â² : âˆ€ {Î±} {A : Set Î±} â†’ A â†’ Â¬ (Â¬ A)
    â†’Â¬Â² a = {!!}

    Â¬Â³â†’Â¬ : âˆ€ {Î±} {A : Set Î±} â†’ Â¬ (Â¬ (Â¬ A)) â†’ Â¬ A
    Â¬Â³â†’Â¬ = {!!}
\end{code}
Hint. Use `C-c C-,` here to see the goal type in its normal form.

From a more logical standpoint the idea of `Â¬` is that false proposition `P` should be isomorphic to `âŠ¥` (i.e. they should imply each other: `âŠ¥ â†’ P âˆ§ P â†’ âŠ¥`).
Since `âŠ¥ â†’ P` is true for all `P` there is only `P â†’ âŠ¥` left for us to prove.

From a computational point of view having a variable of type `âŠ¥` in a context means that there is no way execution of a program could reach this point.
Which means we can match on the variable and use absurd pattern, `âŠ¥-elim` does exactly that.

Note that, being an intuitionistic system, Agda has no means to prove "double negation" rule.
See for yourself:
\begin{code}
    Â¬Â²â†’ : âˆ€ {Î±} {A : Set Î±} â†’ Â¬ (Â¬ A) â†’ A
    Â¬Â²â†’ Â¬Â¬a = {!check me!}
  {- end of ThrowAwayExercise -}
\end{code}

By the way, proofs in the exercise above amounted to a serious scientific paper at the start of 20th century.

Solution for the exercise:
\begin{code}
  private
   module DummyAB {Î± Î²} {A : Set Î±} {B : Set Î²} where
    contradiction : A â†’ Â¬ A â†’ B
    contradiction a Â¬a = âŠ¥-elim (Â¬a a)

    contraposition : (A â†’ B) â†’ (Â¬ B â†’ Â¬ A)
    contraposition = flip _âˆ˜â€²_

    contrapositionÂ¬ : (A â†’ Â¬ B) â†’ (B â†’ Â¬ A)
    contrapositionÂ¬ = flip

  open DummyAB public

  private
   module DummyA {Î±} {A : Set Î±} where
    â†’Â¬Â² : A â†’ Â¬ (Â¬ A)
    â†’Â¬Â² = contradiction

    Â¬Â³â†’Â¬ : Â¬ (Â¬ (Â¬ A)) â†’ Â¬ A
    Â¬Â³â†’Â¬ Â¬Â³a = Â¬Â³a âˆ˜â€² â†’Â¬Â²

  open DummyA public
\end{code}
**Exercise.** Understand this solution.

Note clever module usage.
Opening a module with parameters prefixes types of all the things defined there with these parameters.
We will use this trick a lot.

Let us define conjunction, disjunction, and logical equivalence:
\begin{code}
  -- input for âˆ§ is \and
  record _âˆ§_ {Î± Î²} (A : Set Î±) (B : Set Î²) : Set (Î± âŠ” Î²) where
    constructor _,â€²_
    field
      fst : A
      snd : B

  open _âˆ§_ public

  -- input for âˆ¨ is \or
  data _âˆ¨_ {Î± Î²} (A : Set Î±) (B : Set Î²) : Set (Î± âŠ” Î²) where
    inl : A â†’ A âˆ¨ B
    inr : B â†’ A âˆ¨ B

  -- input for â†” is \<->
  _â†”_ : âˆ€ {Î± Î²} (A : Set Î±) (B : Set Î²) â†’ Set (Î± âŠ” Î²)
  A â†” B = (A â†’ B) âˆ§ (B â†’ A)
\end{code}

Make all this goodness available:
\begin{code}
open Logic public
\end{code}

### MLTT: types and properties

Some definitions from Per Martin-LÃ¶f's type theory [@MartinLoef:ITT-Sambin]:
\begin{code}
module MLTT where
  -- input for â‰¡ is \==
  -- Propositional equality
  infix 4 _â‰¡_
  data _â‰¡_ {Î±} {A : Set Î±} (x : A) : A â†’ Set Î± where
    refl : x â‰¡ x

  -- input for Î£ is \Sigma
  -- Dependent pair
  record Î£ {Î± Î²} (A : Set Î±) (B : A â†’ Set Î²) : Set (Î± âŠ” Î²) where
    constructor _,_
    field
      projl : A
      projr : B projl

  open Î£ public

  -- Make rewrite syntax work
  {-# BUILTIN EQUALITY _â‰¡_ #-}
  {-# BUILTIN REFL    refl #-}
\end{code}

The `Î£` type is a dependent version of `_âˆ§_` (the second field depends on the first), i.e. `_âˆ§_` is a specific case of `Î£`:
\begin{code}
  -- input for Ã— is \x
  _Ã—_ : âˆ€ {Î± Î²} (A : Set Î±) (B : Set Î²) â†’ Set (Î± âŠ” Î²)
  A Ã— B = Î£ A (Î» _ â†’ B)
  
  Ã—â†”âˆ§ : âˆ€ {Î± Î²} {A : Set Î±} {B : Set Î²} â†’ (A Ã— B) â†” (A âˆ§ B)
  Ã—â†”âˆ§ = (Î» z â†’ projl z ,â€² projr z) ,â€² (Î» z â†’ fst z , snd z)
\end{code}

Personally, I use both `_âˆ§_` and `_Ã—_` occasionally since `_Ã—_` looks ugly in the normal form and makes goal types hard to read.

Some properties:
\begin{code}
  module â‰¡-Prop where
   private
    module DummyA {Î±} {A : Set Î±} where
      -- _â‰¡_ is symmetric
      sym : {x y : A} â†’ x â‰¡ y â†’ y â‰¡ x
      sym refl = refl
  
      -- _â‰¡_ is transitive
      trans : {x y z : A} â†’ x â‰¡ y â†’ y â‰¡ z â†’ x â‰¡ z
      trans refl refl = refl
  
      -- _â‰¡_ is substitutive
      subst : âˆ€ {Î³} {P : A â†’ Set Î³} {x y} â†’ x â‰¡ y â†’ P x â†’ P y
      subst refl p = p
  
    private
     module DummyAB {Î± Î²} {A : Set Î±} {B : Set Î²} where
      -- _â‰¡_ is congruent
      cong : âˆ€ (f : A â†’ B) {x y} â†’ x â‰¡ y â†’ f x â‰¡ f y
      cong f refl = refl
  
      substâ‚‚ : âˆ€ {â„“} {P : A â†’ B â†’ Set â„“} {x y u v} â†’ x â‰¡ y â†’ u â‰¡ v â†’ P x u â†’ P y v
      substâ‚‚ refl refl p = p
  
    private
     module DummyABC {Î± Î² Î³} {A : Set Î±} {B : Set Î²} {C : Set Î³} where
      congâ‚‚ : âˆ€ (f : A â†’ B â†’ C) {x y u v} â†’ x â‰¡ y â†’ u â‰¡ v â†’ f x u â‰¡ f y v
      congâ‚‚ f refl refl = refl
  
    open DummyA public
    open DummyAB public
    open DummyABC public
\end{code}

Make all this goodness available:
\begin{code}
open MLTT public
\end{code}

### Decidable propositions

\begin{code}
module Decidable where
\end{code}

*Decidable proposition* it is a proposition that has an explicit proof or disproval:
\begin{code}
  data Dec {Î±} (A : Set Î±) : Set Î± where
    yes : ( a :   A) â†’ Dec A
    no  : (Â¬a : Â¬ A) â†’ Dec A
\end{code}
This datatype is very much like `Bool`, except it also explains _why_ the proposition holds or why it must not.

Decidable propositions are the glue that make your program work with the real world.

Suppose we want to write a program that reads a natural number, say `n`, from `stdin` and divides it by two with `div2E`.
To do that we need a proof that `n` is `Even`.
The easiest way to do it is to define a function that decides if a given natural is `Even`:
\begin{code}
  module ThrowAwayExampleâ‚ where
    open ThrowAwayIntroduction

    Â¬Even+2 : âˆ€ {n} â†’ Â¬ (Even n) â†’ Â¬ (Even (succ (succ n)))
    Â¬Even+2 Â¬en (e2succ en) = contradiction en Â¬en

    Even? : âˆ€ n â†’ Dec (Even n)
    Even? zero        = yes ezero
    Even? (succ zero) = no (Î» ()) -- note an absurd pattern in
                                  -- an anonymous lambda expression
    Even? (succ (succ n)) with Even? n
    ... | yes a       = yes (e2succ a)
    ... | no  aÂ¬      = no (Â¬Even+2 aÂ¬)
  {- end of ThrowAwayExampleâ‚ -}
\end{code}
then read `n` from `stdin`, feed it to `Even?`, match on the result and call `div2E` if `n` is `Even`.

Same idea applies to almost everything:

* Want to write a parser?
Parser is a procedure that decides if a string conforms to a syntax.
* Want to type check a program?
Type checker is a procedure that decides if the program conforms to a given set of typing rules.
* Want an optimizing compiler?
Parse, match on `yes`, type check, match on `yes`, optimize typed representation, generate output.
* And so on.

Using same idea we can define decidable dichotomous and trichotomous propositions:
\begin{code}
  data Di {Î± Î²} (A : Set Î±) (B : Set Î²) : Set (Î± âŠ” Î²) where
    diyes : ( a :   A) (Â¬b : Â¬ B) â†’ Di A B
    dino  : (Â¬a : Â¬ A) ( b :   B) â†’ Di A B

  data Tri {Î± Î² Î³} (A : Set Î±) (B : Set Î²) (C : Set Î³) : Set (Î± âŠ” (Î² âŠ” Î³)) where
    tri< : ( a :   A) (Â¬b : Â¬ B) (Â¬c : Â¬ C) â†’ Tri A B C
    triâ‰ˆ : (Â¬a : Â¬ A) ( b :   B) (Â¬c : Â¬ C) â†’ Tri A B C
    tri> : (Â¬a : Â¬ A) (Â¬b : Â¬ B) ( c :   C) â†’ Tri A B C
\end{code}

Make all this goodness available:
\begin{code}
open Decidable public
\end{code}

### Natural numbers: operations, properties and relations

Consider this to be the answer (encrypted with `rewrite`s) for the exercise way above:
\begin{code}
module Data-â„• where
  -- Natural numbers (positive integers)
  data â„• : Set where
    zero : â„•
    succ : â„• â†’ â„•

  module â„•-Rel where
    infix 4 _â‰¤_ _<_ _>_
  
    data _â‰¤_ : â„• â†’ â„• â†’ Set where
      zâ‰¤n : âˆ€ {n}           â†’ zero â‰¤ n
      sâ‰¤s : âˆ€ {n m} â†’ n â‰¤ m â†’ succ n â‰¤ succ m
  
    _<_ : â„• â†’ â„• â†’ Set
    n < m = succ n â‰¤ m
  
    _>_ : â„• â†’ â„• â†’ Set
    n > m = m < n
  
    â‰¤-unsucc : âˆ€ {n m} â†’ succ n â‰¤ succ m â†’ n â‰¤ m
    â‰¤-unsucc (sâ‰¤s a) = a 
  
    <-Â¬refl : âˆ€ n â†’ Â¬ (n < n)
    <-Â¬refl zero ()
    <-Â¬refl (succ n) (sâ‰¤s p) = <-Â¬refl n p
  
    â‰¡â†’â‰¤ : âˆ€ {n m} â†’ n â‰¡ m â†’ n â‰¤ m
    â‰¡â†’â‰¤ {zero}   refl = zâ‰¤n
    â‰¡â†’â‰¤ {succ n} refl = sâ‰¤s (â‰¡â†’â‰¤ {n} refl) -- Note this
  
    â‰¡â†’Â¬< : âˆ€ {n m} â†’ n â‰¡ m â†’ Â¬ (n < m)
    â‰¡â†’Â¬< refl = <-Â¬refl _
  
    â‰¡â†’Â¬> : âˆ€ {n m} â†’ n â‰¡ m â†’ Â¬ (n > m)
    â‰¡â†’Â¬> refl = <-Â¬refl _
  
    <â†’Â¬â‰¡ : âˆ€ {n m} â†’ n < m â†’ Â¬ (n â‰¡ m)
    <â†’Â¬â‰¡ = contrapositionÂ¬ â‰¡â†’Â¬<
  
    >â†’Â¬â‰¡ : âˆ€ {n m} â†’ n > m â†’ Â¬ (n â‰¡ m)
    >â†’Â¬â‰¡ = contrapositionÂ¬ â‰¡â†’Â¬>
  
    <â†’Â¬> : âˆ€ {n m} â†’ n < m â†’ Â¬ (n > m)
    <â†’Â¬> {zero} (sâ‰¤s zâ‰¤n) ()
    <â†’Â¬> {succ n} (sâ‰¤s p<) p> = <â†’Â¬> p< (â‰¤-unsucc p>)
  
    >â†’Â¬< : âˆ€ {n m} â†’ n > m â†’ Â¬ (n < m)
    >â†’Â¬< = contrapositionÂ¬ <â†’Â¬>
  
  module â„•-Op where
    open â‰¡-Prop
  
    pred : â„• â†’ â„•
    pred zero = zero
    pred (succ n) = n
  
    infixl 6 _+_
    _+_ : â„• â†’ â„• â†’ â„•
    zero   + n = n
    succ n + m = succ (n + m)
  
    infixr 7 _*_
    _*_ : â„• â†’ â„• â†’ â„•
    zero   * m = zero
    succ n * m = m + (n * m)
  
    private
     module Dummyâ‚€ where
      lemma-+zero : âˆ€ a â†’ a + zero â‰¡ a
      lemma-+zero zero = refl
      lemma-+zero (succ a) rewrite lemma-+zero a = refl
    
      lemma-+succ : âˆ€ a b â†’ succ a + b â‰¡ a + succ b
      lemma-+succ zero b = refl
      lemma-+succ (succ a) b rewrite lemma-+succ a b = refl
  
    open Dummyâ‚€
  
    -- + is associative
    +-assoc : âˆ€ a b c â†’ (a + b) + c â‰¡ a + (b + c)
    +-assoc zero b c = refl
    +-assoc (succ a) b c rewrite (+-assoc a b c) = refl
  
    -- + is commutative
    +-comm : âˆ€ a b â†’ a + b â‰¡ b + a
    +-comm zero b = sym $ lemma-+zero b
    +-comm (succ a) b rewrite +-comm a b | lemma-+succ b a = refl
  
    -- * is distributive by +
    *+-dist : âˆ€ a b c â†’ (a + b) * c â‰¡ a * c + b * c
    *+-dist zero b c = refl
    *+-dist (succ a) b c rewrite *+-dist a b c | +-assoc c (a * c) (b * c) = refl
  
    -- * is associative
    *-assoc : âˆ€ a b c â†’ (a * b) * c â‰¡ a * (b * c)
    *-assoc zero b c = refl
    *-assoc (succ a) b c rewrite *+-dist b (a * b) c | *-assoc a b c = refl
    
    private
     module Dummyâ‚ where
      lemma-*zero : âˆ€ a â†’ a * zero â‰¡ zero
      lemma-*zero zero = refl
      lemma-*zero (succ a) = lemma-*zero a
      
      lemma-+swap : âˆ€ a b c â†’ a + (b + c) â‰¡ b + (a + c)
      lemma-+swap a b c rewrite sym (+-assoc a b c) | +-comm a b | +-assoc b a c = refl
      
      lemma-*succ : âˆ€ a b â†’ a + a * b â‰¡ a * succ b 
      lemma-*succ zero b = refl
      lemma-*succ (succ a) b rewrite lemma-+swap a b (a * b) | lemma-*succ a b = refl
    
    open Dummyâ‚
  
    -- * is commutative
    *-comm : âˆ€ a b â†’ a * b â‰¡ b * a
    *-comm zero b = sym $ lemma-*zero b
    *-comm (succ a) b rewrite *-comm a b | lemma-*succ b a = refl

  module â„•-RelOp where
    open â„•-Rel
    open â„•-Op
    open â‰¡-Prop
    
    infix 4 _â‰¡?_ _â‰¤?_ _<?_
  
    _â‰¡?_ : (n m : â„•) â†’ Dec (n â‰¡ m)
    zero    â‰¡? zero   = yes refl
    zero    â‰¡? succ m = no (Î» ())
    succ n  â‰¡? zero   = no (Î» ())
    succ n  â‰¡? succ m with n â‰¡? m
    succ .m â‰¡? succ m | yes refl = yes refl
    succ n  â‰¡? succ m | no Â¬a    = no (Â¬a âˆ˜ cong pred) -- Note this
  
    _â‰¤?_ : (n m : â„•) â†’ Dec (n â‰¤ m)
    zero â‰¤? m = yes zâ‰¤n
    succ n â‰¤? zero = no (Î» ())
    succ n â‰¤? succ m with n â‰¤? m
    ... | yes a = yes (sâ‰¤s a)
    ... | no Â¬a = no (Â¬a âˆ˜ â‰¤-unsucc)
   
    _<?_ : (n m : â„•) â†’ Dec (n < m)
    n <? m = succ n â‰¤? m
  
    cmp : (n m : â„•) â†’ Tri (n < m) (n â‰¡ m) (n > m)
    cmp zero zero     = triâ‰ˆ (Î» ()) refl (Î» ())
    cmp zero (succ m) = tri< (sâ‰¤s zâ‰¤n) (Î» ()) (Î» ())
    cmp (succ n) zero = tri> (Î» ()) (Î» ()) (sâ‰¤s zâ‰¤n)
    cmp (succ n) (succ m) with cmp n m
    cmp (succ n) (succ m) | tri< a Â¬b Â¬c = tri< (sâ‰¤s a) (Â¬b âˆ˜ cong pred) (Â¬c âˆ˜ â‰¤-unsucc)
    cmp (succ n) (succ m) | triâ‰ˆ Â¬a b Â¬c = triâ‰ˆ (Â¬a âˆ˜ â‰¤-unsucc) (cong succ b) (Â¬c âˆ˜ â‰¤-unsucc)
    cmp (succ n) (succ m) | tri> Â¬a Â¬b c = tri> (Â¬a âˆ˜ â‰¤-unsucc) (Â¬b âˆ˜ cong pred) (sâ‰¤s c)

open Data-â„• public
\end{code}
**Exercise.** Understand this. Now, remove all term bodies from `â„•-RelProp` and `â„•-RelOp` and reimplement everything yourself.

### Lists and Vectors

\begin{code}
module Data-List where
  -- List
  infixr 5 _âˆ·_
  data List {Î±} (A : Set Î±) : Set Î± where
    []  : List A
    _âˆ·_ : A â†’ List A â†’ List A

  module List-Op where
  private
   module DummyA {Î±} {A : Set Î±} where
    -- Singleton `List`
    [_] : A â†’ List A
    [ a ] = a âˆ· []

    -- Concatenation for `List`s
    infixr 5 _++_
    _++_ : List A â†’ List A â†’ List A
    []       ++ bs = bs
    (a âˆ· as) ++ bs = a âˆ· (as ++ bs)

    -- Filtering with decidable propositions
    filter : âˆ€ {Î²} {P : A â†’ Set Î²} â†’ (âˆ€ a â†’ Dec (P a)) â†’ List A â†’ List A
    filter p [] = []
    filter p (a âˆ· as) with p a
    ... | yes _ = a âˆ· (filter p as)
    ... | no  _ = filter p as

  open DummyA public

module Data-Vec where
  -- Vector
  infixr 5 _âˆ·_
  data Vec {Î±} (A : Set Î±) : â„• â†’ Set Î± where
    []  : Vec A zero
    _âˆ·_ : âˆ€ {n} â†’ A â†’ Vec A n â†’ Vec A (succ n)
  
  module Vec-Op where
    open â„•-Op
  
    private
     module DummyA {Î±} {A : Set Î±} where
      -- Singleton `Vec`
      [_] : A â†’ Vec A (succ zero)
      [ a ] = a âˆ· []
  
      -- Concatenation for `Vec`s
      infixr 5 _++_
      _++_ : âˆ€ {n m} â†’ Vec A n â†’ Vec A m â†’ Vec A (n + m)
      []       ++ bs = bs
      (a âˆ· as) ++ bs = a âˆ· (as ++ bs)
  
      head : âˆ€ {n} â†’ Vec A (succ n) â†’ A
      head (a âˆ· as) = a
  
      tail : âˆ€ {n} â†’ Vec A (succ n) â†’ A
      tail (a âˆ· as) = a
  
    open DummyA public
\end{code}

\begin{code}
{-
Work in progress. TODO.

I find the following definition quite amusing:

module VecLists where
  open Data-Vec

  private
   module DummyA {Î±} {A : Set Î±} where
     VecList = Î£ â„• (Vec A)
-}
\end{code}

### Being in a `List`

Indexing allows to define pretty fun things:
\begin{code}
module ThrowAwayMoreâ‚ where
  open Data-List
  open List-Op

  -- input for âˆˆ is \in
  -- `a` is in `List`
  data _âˆˆ_ {Î±} {A : Set Î±} (a : A) : List A â†’ Set Î± where
    here  : âˆ€ {as}   â†’ a âˆˆ (a âˆ· as)
    there : âˆ€ {b as} â†’ a âˆˆ as â†’ a âˆˆ (b âˆ· as)
  
  -- input for âŠ† is \sub= 
  -- `xs` is a sublist of `ys`
  _âŠ†_ : âˆ€ {Î±} {A : Set Î±} â†’ List A â†’ List A â†’ Set Î±
  as âŠ† bs = âˆ€ {x} â†’ x âˆˆ as â†’ x âˆˆ bs
\end{code}

The `_âˆˆ_` relation says that "being in a `List`" for an element `a : A` means that `a` in the head of a `List` or in the tail of a `List`.
For some `a` and `as` a value of type `a âˆˆ as`, that is "`a` is in a list `as`" is a position of an element `a` in `as` (there might be any number of elements in this type).
Relation `âŠ†`, that is "being a sublist", carries a function that for each `a` in `xs` gives its position in `as`.

Examples:
\begin{code}
  listTestâ‚ = zero âˆ· zero âˆ· succ zero âˆ· []
  listTestâ‚‚ = zero âˆ· succ zero âˆ· []
  
  âˆˆTestâ‚€ : zero âˆˆ listTestâ‚
  âˆˆTestâ‚€ = here
  
  âˆˆTestâ‚ : zero âˆˆ listTestâ‚
  âˆˆTestâ‚ = there here

  âŠ†Test : listTestâ‚‚ âŠ† listTestâ‚
  âŠ†Test here = here
  âŠ†Test (there here) = there (there here)
  âŠ†Test (there (there ()))
\end{code}

Let us prove some properties for `âŠ†` relation:
\begin{code}
  âŠ†-++-left : âˆ€ {A : Set} (as bs : List A) â†’ as âŠ† (bs ++ as)
  âŠ†-++-left as [] n = n
  âŠ†-++-left as (b âˆ· bs) n = there (âŠ†-++-left as bs n)
  
  âŠ†-++-right : âˆ€ {A : Set} (as bs : List A) â†’ as âŠ† (as ++ bs)
  âŠ†-++-right [] bs ()
  âŠ†-++-right (a âˆ· as) bs here = here
  âŠ†-++-right (a âˆ· as) bs (there n) = there (âŠ†-++-right as bs n)
{- end of ThrowAwayMoreâ‚ -}
\end{code}
Note how these proofs renumber elements of a given list.

### Being in a `List` generalized: Any

By generalizing `_âˆˆ_` relation from propositional equality (in `x âˆˆ (x âˆ· xs)` both `x`s are propositionally equal) to arbitrary predicates we arrive at:
\begin{code}
module Data-Any where
  open Data-List
  open List-Op

  -- Some element of a `List` satisfies `P`
  data Any {Î± Î³} {A : Set Î±} (P : A â†’ Set Î³) : List A â†’ Set (Î± âŠ” Î³) where
    here  : âˆ€ {a as} â†’ (pa  : P a)      â†’ Any P (a âˆ· as)
    there : âˆ€ {a as} â†’ (pas : Any P as) â†’ Any P (a âˆ· as)

  module Membership {Î± Î² Î³} {A : Set Î±} {B : Set Î²} (P : B â†’ A â†’ Set Î³) where
    -- input for âˆˆ is \in
    -- `P b a` holds for some element `a` from the `List`
    -- when P is `_â‰¡_` this becomes the usual "is in" relation
    _âˆˆ_ : B â†’ List A â†’ Set (Î± âŠ” Î³)
    b âˆˆ as = Any (P b) as

    -- input for âˆ‰ is \notin
    _âˆ‰_ : B â†’ List A â†’ Set (Î± âŠ” Î³)
    b âˆ‰ as = Â¬ (b âˆˆ as)

    -- input for âŠ† is \sub=
    _âŠ†_ : List A â†’ List A â†’ Set (Î± âŠ” Î² âŠ” Î³)
    as âŠ† bs = âˆ€ {x} â†’ x âˆˆ as â†’ x âˆˆ bs

    -- input for âŠˆ is \sub=n
    _âŠˆ_ : List A â†’ List A â†’ Set (Î± âŠ” Î² âŠ” Î³)
    as âŠˆ bs = Â¬ (as âŠ† bs)

    -- input for âŠ‡ is \sup=
    _âŠ†âŠ‡_ : List A â†’ List A â†’ Set (Î± âŠ” Î² âŠ” Î³)
    as âŠ†âŠ‡ bs = (as âŠ† bs) âˆ§ (bs âŠ† as)

    âŠ†-refl : âˆ€ {as} â†’ as âŠ† as
    âŠ†-refl = id

    âŠ†-trans : âˆ€ {as bs cs} â†’ as âŠ† bs â†’ bs âŠ† cs â†’ as âŠ† cs
    âŠ†-trans f g = g âˆ˜ f

    âŠ†âŠ‡-refl : âˆ€ {as} â†’ as âŠ†âŠ‡ as
    âŠ†âŠ‡-refl = id ,â€² id
    
    âŠ†âŠ‡-sym : âˆ€ {as bs} â†’ as âŠ†âŠ‡ bs â†’ bs âŠ†âŠ‡ as
    âŠ†âŠ‡-sym (f ,â€² g) = g ,â€² f

    âŠ†âŠ‡-trans : âˆ€ {as bs cs} â†’ as âŠ†âŠ‡ bs â†’ bs âŠ†âŠ‡ cs â†’ as âŠ†âŠ‡ cs
    âŠ†âŠ‡-trans f g = (fst g âˆ˜ fst f) ,â€² (snd f âˆ˜ snd g)

    âˆ‰[] : âˆ€ {b} â†’ b âˆ‰ []
    âˆ‰[]()

    -- When P is `_â‰¡_` this becomes `b âˆˆ [ a ] â†’ b â‰¡ a`
    âˆˆsingletonâ†’P : âˆ€ {a b} â†’ b âˆˆ [ a ] â†’ P b a
    âˆˆsingletonâ†’P (here pba) = pba
    âˆˆsingletonâ†’P (there ())
    
    Pâ†’âˆˆsingleton : âˆ€ {a b} â†’ P b a â†’ b âˆˆ [ a ]
    Pâ†’âˆˆsingleton pba = here pba

    âŠ†-++-left : (as bs : List A) â†’ as âŠ† (bs ++ as)
    âŠ†-++-left as [] n = n
    âŠ†-++-left as (b âˆ· bs) n = there (âŠ†-++-left as bs n)

    âŠ†-++-right : (as : List A) (bs : List A) â†’ as âŠ† (as ++ bs)
    âŠ†-++-right [] bs ()
    âŠ†-++-right (x âˆ· as) bs (here pa) = here pa
    âŠ†-++-right (x âˆ· as) bs (there n) = there (âŠ†-++-right as bs n)

    âŠ†-filter : âˆ€ {Ïƒ} {Q : A â†’ Set Ïƒ} â†’ (q : âˆ€ x â†’ Dec (Q x)) â†’ (as : List A) â†’ filter q as âŠ† as
    âŠ†-filter q [] ()
    âŠ†-filter q (a âˆ· as) n with q a
    âŠ†-filter q (a âˆ· as) (here pa) | yes qa = here pa
    âŠ†-filter q (a âˆ· as) (there n) | yes qa = there (âŠ†-filter q as n)
    âŠ†-filter q (a âˆ· as) n         | no Â¬qa = there (âŠ†-filter q as n)
\end{code}

**Exercise.** Note how general this code is.
`âŠ†-filter` covers a broad set of propositions, with "filtered list is a sublist (in the usual sense) of the original list" being a special case.
Do `C-c C-.` in the following goal and explain the type:
\begin{code}
module ThrowAwayMoreâ‚‚ where
  goal = {!Data-Any.Membership.âŠ†-filter!}
{- end of ThrowAwayMoreâ‚‚ -}
\end{code}
Explain the types of all the terms in `Membership` module.

### Dual predicate: All

\begin{code}
{-
Work in progress. TODO.

I didn't have a chance to use `All` yet (and I'm too lazy to implement this module right now),
but here is the definition:

module Data-All where
  open Data-List
  -- All elements of a `List` satisfy `P`
  data All {Î± Î²} {A : Set Î±} (P : A â†’ Set Î²) : List A â†’ Set (Î± âŠ” Î²) where
    []âˆ€  : All P []
    _âˆ·âˆ€_ : âˆ€ {a as} â†’ P a â†’ All P as â†’ All P (a âˆ· as)
-}
\end{code}

### Booleans

Are not that needed with `Dec`, actually.

\begin{code}
module Data-Bool where
  -- Booleans
  data Bool : Set where
    true false : Bool
  
  module Bool-Op where
    if_then_else_ : âˆ€ {Î±} {A : Set Î±} â†’ Bool â†’ A â†’ A â†’ A
    if true  then a else _ = a
    if false then _ else b = b

    not : Bool â†’ Bool
    not true  = false
    not false = true
    
    and : Bool â†’ Bool â†’ Bool
    and true  x = x
    and false _ = false
    
    or : Bool â†’ Bool â†’ Bool
    or false x = x
    or true  x = true

open Data-Bool public
\end{code} 

### Other stuff

Work in progress. TODO.
We need to prove something from A to Z.
Quicksort maybe.

## Pre-theoretical corner

This section discusses interesting things about Agda which are somewhere in between practice and pure theory.

\begin{code}
module ThrowAwayPreTheory where
  open â‰¡-Prop
  open â„•-Op
\end{code}

### Equality and unification

Rewriting with equality hides a couple of catches.

Remember the term of `lemma-+zeroâ€²` from above:
\begin{code}
  lemma-+zeroâ€² : âˆ€ a â†’ a + zero â‰¡ a
  lemma-+zeroâ€² zero = refl
  lemma-+zeroâ€² (succ a) with a + zero | lemma-+zeroâ€² a
  lemma-+zeroâ€² (succ a) | ._ | refl = refl
\end{code}
it typechecks, but the following proof doesn't:
\begin{spec}
  lemma-+zeroâ€²â€² : âˆ€ a â†’ a + zero â‰¡ a
  lemma-+zeroâ€²â€² zero = refl
  lemma-+zeroâ€²â€² (succ a) with a | lemma-+zeroâ€²â€² a
  lemma-+zeroâ€²â€² (succ a) | ._ | refl = refl
\end{spec}

The problem here is that for arbitrary terms `A` and `B` to pattern match on `refl : A â‰¡ B` these `A` and `B` must unify.
In `lemma-+zeroâ€²` case we have `a + zero` backward-substituted into a new variable `w`, then we match on `refl` we get `w â‰¡ a`.
On the other hand, in `lemma-+zeroâ€²â€²` case we have `a` changed into `w`, an `refl` gets `w + zero â‰¡ w` type which is a malformed (recursive) unification constraint.

There is another catch.
Our current definition of `_â‰¡_` allows to express equality on types, e.g. `Bool â‰¡ â„•`.

This enables us to write the following term:
\begin{spec}
  lemma-unsafe-eq : (P : Bool â‰¡ â„•) â†’ Bool â†’ â„•
  lemma-unsafe-eq P b with Bool | P
  lemma-unsafe-eq P b | .â„• | refl = b + succ zero
\end{code}
which type checks without errors.

Note, however, that `lemma-unsafe-eq` cannot be proven by simply pattern matching on `P`:
\begin{spec}
  lemma-unsafe-eqâ‚€ : (P : Bool â‰¡ â„•) â†’ Bool â†’ â„•
  lemma-unsafe-eqâ‚€ refl b = b
\end{spec}

\begin{code}
{- end of ThrowAwayPreTheory -}
\end{code}

**Exercise.** `lemma-unsafe-eq` is a food for thought about computation safety under false assumptions.

## Theoretical corner

In this section we shall talk about some theoretical stuff like datatype encodings and paradoxes.
You might want to read some of the theoretical references like [@Sorensen-Urzyczyn:lectures-on-curry-howard-isomorphism:1998;@MartinLoef:ITT-Sambin] first.

\begin{code}
module ThrowAwayTheory where
\end{code}

In literature Agda's arrow `(x : X) â†’ Y` (where `Y` might have `x` free) is called *dependent product type*, or Î -type ("Pi-type") for short.
Dependent pair `Î£` is called *dependent sum type*, or Î£-type ("Sigma-type") for short.

### Finite types

Given `âŠ¥`, `âŠ¤` and `Bool` it is possible to define any *finite type*, that is a type with finite number of elements.

\begin{code}
  module FiniteTypes where
    open Bool-Op
    
    _âˆ¨â€²_ : (A B : Set) â†’ Set
    A âˆ¨â€² B = Î£ Bool (Î» x â†’ if x then A else B)
  
    zeroâ€²  = âŠ¥
    oneâ€²   = âŠ¤
    twoâ€²   = Bool
    threeâ€² = oneâ€² âˆ¨â€² twoâ€²
    fourâ€²  = twoâ€² âˆ¨â€² twoâ€²
    --- and so on
\end{code}

TODO. Say something about extensional setting and `âŠ¤ = âŠ¥ â†’ âŠ¥`.

### Simple datatypes

\begin{code}
  module Î Î£-Datatypes where
\end{code}

Given finite types, Î -types, and Î£-types it is possible to define non-inductive datatypes using the same scheme the definition of `_âˆ¨â€²_` uses.

Non-inductive datatype without indexes has the following scheme:
\begin{spec}
data DataTypeName (Param1 : Param1Type) (Param2 : Param2Type) ... : Set whatever
  Cons1 : (Cons1Arg1 : Cons1Arg1Type) (Cons1Arg2 : Cons1Arg2Type) ... â†’ DataTypeName Param1 Param2 ...
  Cons2 : (Cons2Arg1 : Cons2Arg1Type) ... â†’ DataTypeName Param1 Param2 ...
  ...
  ConsN : (ConsNArg1 : ConsNArg1Type) ... â†’ DataTypeName Param1 Param2 ...
\end{spec}

Re-encoded into Î -types, Î£-types, and finite types it becomes:
\begin{spec}
DataTypeName : (Param1 : Param1Type) (Param2 : Param2Type) ... â†’ Set whatever
DataTypeName Param1 Param2 ... = Î£ FiniteTypeWithNElements choice where
  choice : FiniteTypeWithNElements â†’ Set whatever
  choice element1 = Î£ Cons1Arg1Type (Î» Cons1Arg1 â†’ Î£ Cons1Arg2Type (Î» Cons1Arg2 â†’ ...))
  choice element2 = Î£ Cons2Arg1Type (Î» Cons2Arg1 â†’ ...)
  ...
  choice elementN = Î£ ConsNArg1Type (Î» ConsNArg1 â†’ ...)
\end{spec}

For instance, `Di` type from above translates into:
\begin{code}
    Diâ€² : âˆ€ {Î± Î²} (A : Set Î±) (B : Set Î²) â†’ Set (Î± âŠ” Î²)
    Diâ€² {Î±} {Î²} A B = Î£ Bool choice where
      choice : Bool â†’ Set (Î± âŠ” Î²)
      choice true  = A Ã— Â¬ B
      choice false = Â¬ A Ã— B
\end{code}

### Datatypes with indices

Work in progress. TODO.
The general idea: add them as parameters and place an equality proof inside.

### Recursive datatypes

Work in progress. TODO.
General ideas: W-types and Î¼.

#### Curry's paradox

Negative occurrences make the system inconsistent.

Copy this to a separate file and typecheck:
\begin{spec}
{-# OPTIONS --no-positivity-check #-}
module CurrysParadox where
  data CS (C : Set) : Set where
    cs : (CS C â†’ C) â†’ CS C

  paradox : âˆ€ {C} â†’ CS C â†’ C
  paradox (cs b) = b (cs b)

  loop : âˆ€ {C} â†’ C
  loop = paradox (cs paradox)

  contr : âŠ¥
  contr = loop
\end{spec}

### Universes and impredicativity 

Work in progress. TODO.
* Russell's paradox
* Hurkens' paradox

\begin{code}
{- end of ThrowAwayTheory -}
\end{code}

## References