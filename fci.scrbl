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
@(define figure-dir "/home/fare/fare/phdthesis/build")
@(define (figure-table ps) (make-figure-table ps figure-dir))

@author[#:affil-no ""]{@(htmlonlyspace)François-René Rideau}
@; @affil[#:affil-no "1"]{@(htmlonlyspace)TUNES}

@copyright{} @; François-René Rideau}
@doi{} @;10.4230/LIPIcs.xxx.yyy.p}
@volume-info["(SNAPL editors)" "2" "SNAPL 2017" "1" "1" "1"]
@event-short-name{SNAPL 2017}

@title{Reflection with First-Class Implementations}

@abstract{
  We propose an approach to reconcile
  formal methods and computational reflection.
  First, we propose a formalism for computations and implementations,
  and express in it some desirable properties of implementations,
  notably one we dub @emph{observability}.
  Next, we propose a protocol based on first-class implementations that
  enables zoom up and down the abstraction levels of a computation,
  @emph{at runtime}.
  Then we suggest how such a protocol can
  generalize well-known software techniques and
  trivialize some difficult ones (like code migration);
  Finally, we envision how making virtualization a first-class
  programming construct enables a new software architecture.
}

@subject-classification["F.3.2"]{@(htmlonlyspace)Semantics of Programming Languages}
@subject-classification["D.3.3"]{@(htmlonlyspace)Language Constructs and Features}

@keywords{
  First-class implementations,
  Reflection
}

@section{Introduction}

@subsection{Category Theory}
We use Category Theory to formalize computation,
but only in elementary ways that require no prior knowledge of it.
Here is a summary of the concepts used in this article.

A @emph{category}
(a) contains a set @L{Node} of nodes (or @emph{objects}), and
for any pair of nodes @L{x, y} a set @L{Arrow x y} of arrows
(or @emph{morphisms}) connecting @L{x} @; (its @emph{domain})
to @L{y}, @; (its @emph{codomain}),
(b) is closed under @emph{composition} of arrows,
whereby given nodes @L{x, y, z : Node} and
arrows @L{f : Arrow x y} and @L{g : Arrow y z},
there is an arrow @L{g @(circ) f : Arrow x z}, and
(c) contains for every node @L{x} an arrow @L{identity x : Arrow x x},
that is neutral for composition left or right.

A @emph{functor} maps the nodes and arrows of one category to
those of another, preserving the composition structure of arrows
(and any additional structure, if applicable).
A category @L{B} is a @emph{subcategory} of @L{A}
if @L{B}'s nodes and arrows are subsets of @L{A}'s, respectively.
@L{B} is said to be a @emph{full} subcategory if for any @L{x, y} in @L{B.Node}
(and thus also in @L{A.Node}), @L{B.Arrow x y = A.Arrow x y}.

@section{Implementations}

@subsection{Computations as Categories}

We consider a @emph{computation} as a category in which
nodes are the potential states of the computation and
arrows are the transitions between those states;
arrows between the same nodes are distinguished by their side-effects if any.
This approach has two advantages:
(1) it unifies a wide range of popular formalisms, including
operational semantics, labeled transition systems, term rewriting,
modal logic, partial orders, etc.;
(2) by using the versatile mathematical tool that is category theory,
we get many structural theorems @q{for free},
including the ability to extract programs from proofs
using the Curry-Howard correspondance.

An @emph{interpretation} of a concrete computation @m{C} as
an abstract computation @m{A} is
a @emph{partial} functor @(Phi) from @m{C} to @m{A}.
An @emph{implementation} of @m{A} with @m{C} is the inverse @; (as a profunctor)
of an interpretation of @m{C} as @m{A},
i.e. it is a non-deterministic partial injective co-functor.
Interpretations are the morphisms of a category of computations;
implementations are the morphisms of its dual category.

Partiality expresses the fact that most computation states and transitions
are intermediate states with no direct meaning
in the abstract computation, as in the proverbial
non-atomic transfer of resources between two owners;
only @emph{observable} concrete states can be interpreted
as having an abstract @emph{meaning}.
Partiality allows discrete computations to be implemented with
continuous computations, infinite ones with finite ones,
the non-deterministic with the deterministic, etc., and vice-versa.
Now, category theory is usually presented in terms of total functions,
so we define a partial functor @(Phi) from @m{C} to @m{A} as the data of
(1) a full subcategory @m{O} of the observable states of @m{C}, and (2) a
(total) functor @m{@(phi) : O → A}.

In general the nodes of a computation encode dynamic execution state such as
registers, bindings, mutable store, call stacks,
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
as in @(Figure-ref "fig-properties").
In these diagrams: (a) horizontal arrows are arrows in a computation
(morphism of the category), with evaluation time running from left to right;
(b) vertical arrows are interpretation arrows, pointing up,
with abstract system on top and concrete system at the bottom;
note that in the above diagrams these vertical arrows are associations
rather than function declarations;
also note that implementation arrows would be pointing down,
but we show interpretation arrows instead
because @emph{they} are functorial, i.e. preserve structure;
(c) in black are the hypotheses of the property, in blue are its conclusions
(assuming the property holds).

The most basic property is @emph{soundness}:
if the concrete implementation includes a transition @m{g} from @m{c} to @m{c'}
and @m{c} is observable with interpretation @m{a} while
and @m{c'} is observable with interpretation @m{a'},
then there is a valid transition @m{f} from @m{a} to @m{a'} such that
@m{@(Phi)(g) = f}.
In other words, if an (intermediate or final) answer
is reached using the concrete computation,
the answer must be correct in the abstract computation.
This property is so fundamental that it is actually implied
by our construction of interpretations as a partial functor.

Many other properties are not as ubiquitous, but still desirable.
For instance, @emph{totality}
(NB: of the implementation, not of the interpretation)
means that given an abstract state @m{a}
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

For instance, we saw above that the computational content of observability is
an actual synchronization primitive that enables the retrieval
of an abstract state from an interrupted concrete computation.
The specification in Agda would look something like this:
@verbatim|{
observe : ∀ {c : C.Node} {a : A.Node} {interpret.node c a}
  (c' : C.Node) {f : C.Arrow c c'} →
  ∃ (λ {c'' : C.Node} → ∃ (λ (g : C.Arrow c c'') →
  ∃ (λ {a'' : A.Node} → ∃ (λ {h : A.Arrow a a''} →
  ∃ (λ {not-advancing g} → interpret.arrow (C.compose g f) h)))))
}|
The simplified computational content would have a type as follows,
with all the logical specification being implicit that the argument node @m{c'}
was reached by starting from an observable node @m{c},
that the returned arrow starts at the same node @m{c'},
ends at an observable node @m{c''},
and is in the not-advancing subcategory @m{C^0} of @m{C}:
@verbatim{observe : C.Node → C.Arrow}

By applying this extraction strategy systematically, we obtain a protocol
to deal with implementations as first-class objects,
where each property defines a trait for typeclasses of implementations,
and suitable typeclasses define categories of computations and implementations.
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
  "fig-tower"
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
the underlying hardware (or physical universe). See @Figure-ref{fig-tower}.

A naïve user could view a compiler as implementing his user-provided source code
being an abstract computation @m{A} with some object code @m{C}.
But the source code @m{S} is only
a representation of the actual abstract computation @m{A} desired by the user;
this computation is defined up to an equivalence class, so
an optimizing compiler can rewrite it into any of the equivalent computations.
However, the equivalence class @m{A} is not computable,
whereas the model @m{U} of equivalences understood by the compiler is;
between the two is thus an irreducible @emph{semantic gap}
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
with an interpretation @(Phi);
and if @(Phi) is @emph{observable}, then @m{C} can be interrupted,
an abstract state can be retrieved from its concrete state,
and can be recompiled to another computation @m{K}
with an interpretation @m{\Psi},
from which the computation resumes @emph{with all its dynamic state}.
Of course, any intermediate representation of states of @m{A} can hopefully
be optimized away when compiling @m{@(Psi)^{-1}@(circ)@(Phi)};
but as a fallback, it is trivial to implement this migration naïvely.
@; (which should be only a constant factor slowdown in the cases that
@; the entire data should be copied and sent over anyway.)

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

Interacting with software is usually limited to adding semantic layers
@emph{on top} of a rigid semantic tower provided to the users ---
through I/O, configuration, sometimes involving translating front-ends.
In its general form, migration consists in interacting with software
by changing semantic layers @emph{below}.
Migration is not limited to changes @q{at the bottom},
by adding one virtualization layer;
it can happen at any intermediate level, by adding, removing, modifying
any implementation layer (or slice of consecutive layers) anywhere,
discarding the entire bottom of the tower if needs be
--- all while the software is running, without losing dynamic state.

@subsection{Natural Transformations}

Code instrumentation, tracing, logging, profiling, single-stepping,
omniscient (time-travel) debugging, code and data coverage, access control,
concurrency control, optimistic evaluation, orthogonal persistence,
virtualization, macro-expansion, etc., are useful development tools
that usually are written at great cost in an ad hoc way.
They then have to be re-implemented for every semantic tower;
and most of them are effectively lost in most cases
when adding a semantic layer on top, at the bottom or in between.
Developers thus have good tooling only as long as the issues they face
happen at the abstraction level supported by their development system;
if they happen at a higher or lower level, the quality of their tooling
drops back to zero.

We conjecture that all these techniques can be seen as
@emph{natural transformations} of implementations (viewed as profunctors).
They can thus be written in a generic way that applies to all implementations
that expose a suitable extension of our first-class implementation protocol.
They can then be made automatically available to all computations
developed using our formalism, and preserved when
adding, removing or recomposing semantic layers in arbitrary ways.

Therefore, a developer could start a program,
notice some weird behavior when some conditions happen,
enable time-travel debugging to explain the behavior,
zoom into lower levels of abstraction if needed, or out of them if possible,
and locate the bug --- all while the program is running,
with a guarantee that observing the program doesn't modify its behavior.
Similarly, orthogonal persistence could be provided efficiently
@emph{by default} to all computations,
without developers being required to add special hooks;
and users could modify the parameters of their computations
including persistence as their needs change
or the market for cloud providers evolves ---
all of that @emph{at runtime} without losing data.


@section{Reflective Architecture}

@subsection{First-Class Semantic Tower}

To fully take advantage of our approach, we envision a system where
all layers extend our first-class implementation protocol.
Not only must programming languages or their libraries
provide suitable primitives;
moreover, interactive systems, whether Emacs, some integrated development
environment, some operating system shell, some distributed middleware,
or even operating system API, etc.,
must provide dynamic access to this protocol ---
or be wrapped in an abstraction that does.

At runtime, the system will maintain for every computation
a first-class semantic tower:
a category of abstraction levels to which the computation may be migrated.
In that category are distinguished
(1) the topmost computation that is being computed,
that is fixed, specifies the desired semantics of the tower,
and limits the access rights of all implementations,
(2) and the bottommost computation that currently implements the above,
that can be arbitrarily changed within those access rights, and
(3) between the two (and optionally also above the first one),
the @q{current tower} of levels into which the current implementation
can be interpreted without needing to migrate.

Now, it is usually desirable for migration
to happen automatically as directed by an external program,
rather than to be manually triggered by the user,
or rather than to follow a hardwired heuristic.
The user couldn't care less about
most details that migration deals about, whether managing cache lines,
JIT representation of code or data, or availability of cloud resources;
and a heuristic hardwired in the computation itself would make
the computation both more complex and more rigid than necessary.
Thus, every computation has its @emph{controller} that can dynamically
interact with the implementation and incrementally or totally migrate it,
based on whatever signals are relevant.

Actually, the bottommost computation of a semantic tower is itself
the topmost computation of another tower
(which will be trivial only if hittting the @q{bare metal}), so that
there is a tower of controllers that follows a tower of
distinguished current implementations.
And the controller can itself be a pretty arbitrary computation.
All these @q{slices} of a computation may or may not be handled
by the same party;
the end-user, application writer, compiler vendor,
cloud provider, hardware designer, and many more,
are each responsible for their slice of computation,
constrained to implement the upper level with the lower one.

@subsection{Performance and Robustness}

Factoring a computation @q{vertically} in @q{horizontal} implementation slices
as well as in as @q{horizontally} in @q{vertical} modules of functionality
is, we believe, a powerful paradigm for organizing software.
It promises simpler software, with less development effort, more code reuse,
easier proofs of correctness, better defined access rights,
and more performance.

For instance, a computation producing video and sound output can be well
separated from the software that plays it to the user.
This separation also enables redirection of video and sound output
without the application even having to know about it:
the application can keep producing video and sound,
oblivious to where they are output;
the user can seamlessly redirect the output from one device to another,
or broadcast it to an adjustable set of devices,
while the computation is running.
From the point of view of the application, I/O effects are declared
using something akin to a free monad,
with all effects handled by the controller, a separate program,
drastically simplifying the application.

There is obviously a cost in maintaining a semantic tower
and a controller for every computation;
but there is also a performance benefit,
directly related to the semantic simplification:
implementations can directly bang bits to the proper devices
or otherwise directly communicate with each other or inline calls,
and there needs be no extra copying, marshalling,
or sources of slowness and high latency at any moment.
Indeed, data routing, access control, code and data versioning and upgrade,
etc., can now be resolved at a combination of compile-time and link-time,
that can happen dynamically when the implementation is migrated,
taking all dynamic data (including access rights, available formats, etc.)
into account.
Low-level code can be generated
after protocol negotiation and environmental bindings,
rather being generated before and then have to go
through indirections or conditional dispatch at every access.
In many cases, a lot of computation can be eschewed that is not needed
in the current configuration: for instance, video need not even be fully
decoded or frames generated for a window that is not exposed,
or music played when the sound is muted;
yet the moment that the controller migrates the computation back to
being visible or audible, these will be generated again ---
without the application programmer having to explicitly take
these cases into consideration.

Beyond performance, robustness also benefits from
the reflective factoring of computations into slices:
applications can contain much less code,
and their correctness and security properties are potentially
much easier to tighten, enforce and verify, compared to traditional systems.
Controller metaprograms that handle, e.g., video output,
may remain relatively big and hard to ensure the robustness of ---
but they can still be smaller and easier to ascertain
when broken into independent controller meta-objects than
combined as libraries into a big program
with a combinatorial explosion of potential interactions.
And there needn't be the performance penalty of a runtime interpreter
running as a server in a separate process.


@subsection{Social Architecture}

The main benefit we envision for a reflective architecture is in
how it enables a different social organization of developers,
around more modular software.

Without reflection, a developer writes an @q{application} that provides
the entire semantic tower from the user-visible top
to the @q{bottom} provided by the operating system.
Virtualizing that bottom and doing something with it, while possible,
takes advanced system administration skills.
Not having resources to manage (much less develop and debug)
the combinatorial explosion of potential implementation effects
that users may desire, application developers can but offer
sensible defaults for the majority of their users, and
limited configuration for slightly more advanced users.

With reflection, there is no more fixed bottom for software.
All software by construction runs virtualized, except not at the CPU level,
but instead at the level of whatever language it's written in,
under control of its controller.
Developers do not have to care about persistence and other
@q{non-functional requirements} (so-called),
and users do not have to be frustrated because their requirements
are not served by developers.
Orthogonal persistence, infinite undo, time-travel, search, and all kinds
of other services that can be implemented once as natural transformations
are made available @q{for free} to all programs,
under the control of the user,
with an infinite variety of parameters (and sensible defaults),
while developers do not have to care about any of the above.

We anticipate that with a reflective architecture, developers will have
to write less code, of better quality and wider applicability,
while users get to enjoy more functionality better adapted to their needs.
Software will not be organized as @q{applications} but as @q{components};
that interact with each other more like Emacs packages or browser plugins,
except with principled ways of keeping software modular.


@section{Conclusion and Future Work}

The ideas presented in this paper remain largely unimplemented.
Our most solid contribution so far are this trivial unifying formalism
for programming language semantics, and the key notion of @emph{observability}
neglected in existing systems.
The rest is prospective --- but we hope that these prospects will inspire
you to pursue this line of research.
Our plan is to finish a larger document presenting these ideas, then
to implement support for first-class implementations in Racket
or some other Lisp system.


@; full abstraction.
@; @hyperlink["https://common-lisp.net/"]{Common Lisp}, @; XXX @~cite[CLHS]

@(generate-bib)
