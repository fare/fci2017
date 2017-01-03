#lang at-exp lipics
@;-*- Scheme -*-

@(require
   latex-utils/scribble/math
   (except-in scribble/base author)
   scribble/core
   scribble/decode
   scribble/decode-struct
   scribble/html-properties
   (except-in scribble/manual author)
   scribble/manual-struct
   scribble/tag
   scriblib/autobib
   scriblib/figure
   scriblib/footnote
   "bibliography.scrbl"
   "utils.rkt")

@;; This directory contains .pdf for the figures...
@(define build-dir "/home/fare/fare/phdthesis/build")
@(define (figure-table ps)
   (tabular
     (list
       (separate-list (spacing)
         (map (λ (x) (centered (image
                       (format "~a/fig-~a.pdf" build-dir (car x)))))
              ps))
       (separate-list (spacing)
         (map (λ (x) (centered (cadr x))) ps)))))

@author[#|#:affil-no "1"|#]{François-René Rideau}
@;@affil[#:affil-no "1"]{TUNES}

@copyright{François-René Rideau}
@doi{10.4230/LIPIcs.xxx.yyy.p}
@volume-info["(editors)" "2" "SNAPL 2017" "1" "1" "1"]
@event-short-name{SNAPL 2017}

@title{First-Class Implementations}

@abstract{
We propose an approach to reconcile formal methods and computational reflection.
First we formalize a notion of implementation between two computations,
and a few key desirable properties of these implementations,
notably a notion we call observability.
We then propose a protocol based on first-class implementations that
enables navigation up and down the semantic tower of a computation
@emph{at runtime}.
We suggest how such a protocol can
generalize many well-known software techniques and
trivialize some difficult ones (like code migration).
Finally we envision how making virtualization a first-class
programming construct enables a new software architecture.
}

@subject-classification["F.3.2" "Semantics of Programming Languages"]
@subject-classification["D.3.3" "Language Constructs and Features"]

@keywords{
first-class implementations,
reflection,
}

@section{Implementations}

@subsection{Computations as Categories}

We formalize a @emph{computation} as a category in which
nodes are the potential states of the computation and
arrows are the transitions between those states;
arrows between the same nodes are distinguished by their side-effects if any.
This approach has three advantages:
(1) it unifies a wide range of popular formalisms, including
operational semantics, labeled transition systems, term rewriting,
modal logic, partial orders, etc.;
(2) it gives us many structural theorems @q{for free};
(3) it lends itself to extracting programs from proofs.
@; (which we will later take advantage of.)

An @emph{interpretation} of a concrete computation @m{C} as
an abstract computation @m{A} is
a @emph{partial} functor @m{\Phi} from @m{C} to @m{A}.
An @emph{implementation} of @m{A} with @m{C} is the inverse @; (as a profunctor)
of an interpretation of @m{C} as @m{A},
i.e. it is a non-deterministic partial injective co-functor.
Interpretations (resp. implementations) are the morphisms of
a category of computations (resp. its dual).

Partiality expresses the fact that most computation states and transitions
are intermediate states with no direct meaning
in the abstract computation, as in the proverbial
non-atomic transfer of resources between two accounts;
only @emph{observable} concrete states can be interpreted
as having an abstract meaning.
Partiality allows discrete computations to be implemented with
discrete computations, infinite ones with finite ones,
non-deterministic with deterministic ones, etc., and vice-versa.
However, category theory is usually presented in terms of total functions,
so we define a partial functor @m{\Phi} from @m{C} to @m{A} as the data of
(1) a full @note{
  Full means it is a subset of the nodes with all the arrows between them.
  @; as characterized by the canonical full embedding @m{j : O → C}).
} subcategory @m{O} of the observable states of @m{C},
and (2) a (total) functor @m{\phi : O → A}.
@XXX{
  Equivalently, the partial functor can be defined as
  a span from @m{C} to @m{A} where the functor to @m{C} is a full embedding,
  or as a special case of a profunctor.}

In general the nodes of a computation encode dynamic execution state such as
registers, bindings, mutable heap contents, call stacks,
messages sent and received, etc.
An implementation is injective;
it must distinguish the states it implements, and cannot lose that information,
though it can add implementation details and drop alternatives not taken.
Conversely, interpretations may lose information,
introduce approximations, or add alternatives --- and indeed include
static analysis, type systems and abstract interpretation, that do.
@XXX{
Many familiar properties of these interpretations can be stated simply
in the categorical framework.
For instance, a type system with the subject reduction property is one where
there are no arrows between distinct nodes in the abstract category, and
the interpretation functor thus maps all states (concrete nodes)
reachable from a given initial state to the same type (abstract node).
}


@subsection{Properties of Implementations}

@(figure
  "fig-properties"
  "A few properties that any given implementation may or may not possess"
  (figure-table
   '(("soundness" "Soundness")
     ("totality" "Totality")
     ("completeness" "Completeness")))
  (figure-table
   '(("boundedLiveness" "Bounded Liveness")
     ("observability" "Observability"))))

We identify several common desirable properties
for implementations to possess.
We outlined elsewhere how to formalize them in Agda,
together with many variants;
but we like to illustrate the simpler properties
as in @(Figure-ref "fig-properties"):
in these diagrams, horizontal arrows are arrows in a computation
(morphism of the category), running from left to right;
vertical arrows are association by the interpretation partial functor,
with abstract system on top and concrete system at the bottom;
in black are the hypotheses of the property, in blue are its conclusions
(assuming the property holds).

The most basic property is @emph{soundness}:
if the concrete implementation includes a transition @m{g} from @m{c} to @m{c'}
and @m{c} is observable with interpretation @m{a} while
and @m{c'} is observable with interpretation @m{a'},
then there is a valid transition @m{f} from @m{a} to @m{a'} such that
@m{\Phi(g) = f}.
In other words, if a (partial) answer is reached using the concrete computation,
the answer must be correct in the abstract computation.
This property is so fundamental that it is actually implied
by our construction of @m{\Phi} as a partial functor.

Many other properties are not as ubiquitous, but still desirable.
For instance, @emph{totality} means that given an abstract state @m{a}
you can find a concrete state @m{c} that implements it.
Implementations need not be total (and obviously cannot be
when implementing an infinite computation using a finite computer).
However, when composing many layers of implementations,
it is good if non-totality (or failure to satisfy whichever other property)
can be restricted to a single layer, or a few well-identified layers
(e.g. from running out of memory, or from exploring only a subset of
possible choices in case of non-determinism or I/O, etc.).

@emph{Completeness} enables the high-level user to arbitrarily influence
low-level evaluation.
In labeled transition systems, it means the implementation matches
the usual notion of a @emph{simulation}. @; @~cite[Simulation] XXX
It is essential for debugging, but has many other uses;
notably, observability below is not composable,
but the conjunction of observability and completeness is.

There are many variants of @emph{liveness}, the property says that
for @q{long enough} runs of the concrete computation,
the abstract computation will have advanced @q{some}.
One constructive variant, @emph{bounded liveness},
assumes some additive metric for each of
the abstract and concrete computation, and states that
runs above a minimum length @m{l_c} in the concrete computation,
though they may not reach an observable state,
must run @q{past} an observable state that can be interpreted as
a run above a minimum length @m{l_a} in the abstract computation.

Now, our biggest contribution is the notion of @emph{observability},
that allows to retrieve an abstract computation state from an arbitrary
concrete computation state, by first synchronizing to an observable state
through a narrow enough subset @m{C^0} of @m{C}
(that e.g. doesn't involve blocking on I/O or
spending more than a fixed amount of some resources).
Indeed, when a concrete computation is interrupted,
it will in general be in an intermediate state that is not observable
and cannot be interpreted as having an abstract meaning:
it may be in the middle of a transaction;
it may comprise the state of multiple threads
none of which is in an observable state;
the probability of any reachable state being observable may be negligible,
or even be absolutely zero.
Even if the compiler kept a trace of the interpretation function through
which its correctness could be proven, there could be no observable state
to which to apply it... unless the implementation has @emph{observability};
then it is just a matter of using the property to extract
an abstract state @m{a''} from the state @m{c'}
of an interrupted concrete computation.
Observability generalizes PCLSRing @~cite[PCLSRing],
as well as many ad-hoc techniques used to implement
garbage collection or database transactions.


@section{First-Class Implementations}

@subsection{Protocol Extraction}

We can write specifications for our properties with dependent types,
and constructive proofs of the properties
will have a useful computational content.
By erasing type dependencies, implicit arguments and compile-time values,
we can also get a less precise type
suitable for use in run-of-the-mill typed programming languages.

For instance, we saw above that the computational contents of observability is
an actual synchronization primitive that enables the retrieval
of an abstract state from an interrupted concrete computation.
The specification in Agda would look something like that:
@verbatim|{
observe : ∀ {c : Concrete.Node} {a : Abstract.Node} {interpret.Node c a}
  (c' : Concrete.Node) {f : Concrete.Arrow c c'} →
  ∃ (λ {c'' : Concrete.Node} → ∃ (λ (g : Concrete.Arrow c c'') →
  ∃ (λ {a'' : Abstract.Node} → ∃ (λ {h : Abstract.Arrow a a''} →
  ∃ (λ {not-advancing g} → interpret.arrow (Concrete.compose g f) h)))))
}|
The simplified computational contents would have a type as follows,
with all the logical specification being implicit that the argument node @m{c'}
was reached by starting from an observable node @m{c},
that the returned arrow starts at the same node @m{c'},
ends at an observable node @m{c''},
and is in the not-advancing subcategory @m{C^0} of @m{C}:
@verbatim{observe : Concrete.Node → Concrete.Arrow}

By applying this extraction strategy systematically, we obtain a protocol
to deal with implementations as first-class objects,
where each property defines a trait for typeclasses of implementations,
and suitable typeclass define categories of computations and implementations.
Actually, we obtain two protocols:
in the first, @emph{reified} protocol,
nodes @emph{and arrows} of the computations remain first-class objects and
@q{running} the computation is a matter of formal reasoning,
with any side-effects being representations;
in the second, @emph{reflective} protocol,
the concrete computation is the @q{current} ambient computation,
and running it causes side-effects to @q{actually} happen
(as far as the metaprogram manipulating
the represented computation is concerned).
The key functions to switch between these two protocols are
@tt{perform.node: Node → State} and
@tt{perform.arrow: Arrow → State → Effect State} where
@tt{Effect} is a suitable monad --- and their @q{inverses}
@tt{record.node: State → Node} and
@tt{record.arrow: State → (State → Effect State) → Effect Arrow}.
The reflective protocol enables navigation up and down
a computation's semantic tower --- while it is running.


@subsection{The Semantic Tower}

@(figure
  "fig-compilation"
  "A few ways to think about implementations"
  (figure-table
   `(("decomposing" "Composition")
     ;;("compilationxI" "Implementation")
     ;;("compilationxII" "Compilation 2")
     ("compilationxIII" "Compilation")
     ("abstractInterpretation" "Static analysis"))))

Modeling computations as first-class categories
can shed a new light on familiar processes.

Implementations can be composed and decomposed: thus,
complex implementations can be broken down into
many simple passes of compilation;
languages can be implemented by composing a layer on top of previous ones;
and instrumentation or virtualization can be achieved
by composing new layers at the bottom.
Computations are thus part of a @emph{semantic tower}, made of all the layers
composed between the abstract computation specified by the user and
the underlying hardware (or physical universe).

A naïve user could view a compiler as implementing his user-provided source code
being an abstract computation @m{A} with some object code @m{C}.
But the source code @m{S} is only
a representation of the actual abstract computation @m{A} desired by the user;
this computation is defined up to an equivalence class, so
an optimizing compiler can rewrite it into any of the equivalent computations.
However, the equivalence class @m{A} is not computable,
but the model @m{U} of equivalences understood by the compiler is,
so between the two is an irreducible @emph{semantic gap}
that algorithms can never fill.
Now you can add static analysis to the picture, whereby some source programs
can be proven to be in a subset where all nodes have static type @m{\tau},
at which point specialized variants @m{A_\tau}, @m{U_\tau} and @m{C_\tau}
can be used based on this knowledge.

Many other topics can be reviewed in this light.
Tweaking optimizations is about modifying @m{U} in the above model.
Refactoring is changing @m{S} while keeping @m{U} constant.
Developing is modifying @m{A} as being the user's desired approximation
of the trivial abstract computation @m{\top} on top of all semantic towers.
Aspect-oriented programming becomes constraint logic metaprogramming
whereby multiple computations @m{A_i} each have a forgetful interpretation
to a joint computation @m{J}, and a concrete computation @m{C} is sought that
simultaneously implements all of them (and makes the diagram commute).
In general the tower is not a linear total order, but an arbitrary category,
where developers may focus on some aspects and ignore others depending on
the level of abstraction at which appear the issues they are battling with.

And now this semantic tower can be explored and modified at runtime,
explicitly by the user, or implicitly by his software proxies.

@section{Runtime Reflection}

@subsection{Migration}

Our reflective protocol trivializes the notion of code @emph{migration}:
a given abstract computation @m{A} can be implemented with a computation @m{C}
with an interpretation @m{\Phi};
and if @m{\Phi} is @emph{observable}, then @m{C} can be interrupted,
an abstract state can be retrieved from its concrete state,
and can be recompiled to another computation @m{K} with an interpretation @m{\Psi},
from which the computation resumes @emph{with all its dynamic state}.
Of course, any intermediate representation of states of @m{A} can hopefully
be optimized away when compiling @m{\Psi^{-1}\circ\Phi};
but as a fallback, it is trivial to implement this migration naïvely.

Many existing phenomena can be seen as migration:
obviously, moving processes from one computer to another while it's running;
which given a high-level language can now be done
despite very different hardware architectures,
without introducing some slow common virtual machine.
But Garbage Collection can also be seen as a change of representation
of an abstract graph using addressed memory cells.
Process synchronization can be seen as observing a collection of
two (or more) processes as a shared abstract computation then switching back
to a concrete view after effecting the high-level communication.
Zero-copy routing can be seen as changing the interpretation function
regarding who owns the buffers and what they mean, without copying any bits.
JIT compilation, software upgrade (including database schema upgrade),
dynamic refactoring, can be viewed as migration.

Our conceptual framework will hopefully make it easier to develop these
difficult transformations in a provably correct way,
and to automate migration, refactoring, upgrade, optimization, etc.,
of server processes without loss of service or corruption of data
when the short useful life of the underlying software and hardware stacks
is all too predictable.

@subsection{Natural Transformations}

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.


@section{Reflective Architecture}

@subsection{First-Class Semantic Tower}

@subsection{Expected Benefits}



@section{Conclusion and Future Work}

The key concept missing in existing system is a general notion of observability.

@; @hyperlink["https://common-lisp.net/"]{Common Lisp}, @; XXX @~cite[CLHS]

@(generate-bib)
