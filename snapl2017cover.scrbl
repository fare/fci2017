#lang at-exp scribble/base
@;-*- Scheme -*-

@(require
   scribble/core
   scribble/decode
   scribble/decode-struct
   scribble/html-properties
   scribble/manual
   scribble/manual-struct
   scribble/tag
   scriblib/autobib
   scriblib/figure
   scriblib/footnote
   "bibliography.scrbl"
   "utils.rkt")

@author{François-René Rideau}

@title{SNAPL 2017 submission: @(linebreak) Reflection with First-Class Implementations}

@;@raw-latex{\pagestyle{empty}}

@section{Affiliation}

Although I currently work at Bridgewater Associates, this work is my own.
It is the executive summary of my old PhD thesis,
that I stopped 16 years ago, and @hyperlink["http://j.mp/FarePhD"]{am now resurrecting}.


@section{Justification Statement}

The present work passes, though admittedly barely,
the high-standards of formal quality of SNAPL:
its use of category theory to unify various paradigms of semantics is quite elementary,
but the notion of @emph{observability} it introduces alone is worth publication
--- indeed, it provides a solid generalization of many ad hoc concepts
@hyperlink["http://fare.tunes.org/tmp/emergent/pclsr.htm"]{known for a long time by practitioners}
yet never previously theorized and unified (that I know of).

However what makes this work appropriate for SNAPL is the world of new applications
opened by this notion of observability:
it provides solid semantic grounding for the field of computational reflection,
that up until now had minimal justification in programming language semantics;
and it provides a vision for how bringing together these two fields
can enable progress in software architecture and rekindle the "systems" paradigm
(see Dick Gabriel's
@hyperlink["https://www.dreamsongs.com/Files/Incommensurability.pdf"
]{The Structure of a Programming Language Revolution}).

Vision enabled by semantics --- this work fits squarely within the topic of SNAPL.


@section{Attendance Statement}

Should this paper be accepted,
it will be my great honor to come present it and discuss it at SNAPL.
Since this is a personal work, I do not require manager approval,
and will take days off work as needed.
This is my commitment.

I am not a great presenter by any means, but I am at least a passable one,
and I already presented an earlier version of this work
at a monthly @hyperlink["https://youtu.be/heU8NyX5Hus"]{BostonHaskell meeting in 2016}.
If accepted, I will rehearse and work on improving my presentation based on local feedback.


@XXX{
@section{Salutations}

With the hope of meeting you in person at SNAPL,

yours truly,

François-René Rideau, 2017-01-05
}
