#lang at-exp racket
;;-*- Scheme -*-

(require
  scribble/base
  scribble/bnf
  scribble/core
  scribble/decode
  scribble/manual
  scriblib/autobib
  scriblib/footnote
  (for-syntax syntax/parse))

(provide (all-defined-out))

(define (note-url url)
  (note (hyperlink url url)))


(define extended-url "http://fare.tunes.org/files/asdf3/asdf3-2014.html")

(define variant (make-parameter '#:extended))
(define (extended?) (eq? (variant) '#:extended))
(define-syntax-rule (extended-only x ...) (when (extended?) (list x ...)))
(define-syntax-rule (short-only x ...) (unless (extended?) (list x ...)))
(define (appref tag alt)
  (if (extended?)
      (secref tag)
      (hyperlink (string-append extended-url "#" tag) alt)))

(define backend (make-parameter '#:html))
(define-syntax-rule (html-only x ...) (and (eq? (backend) '#:html) (list x ...)))
(define-syntax-rule (pdf-only x ...) (and (eq? (backend) '#:pdf) (list x ...)))

(define multiple-sections (make-parameter #f))
(define include-asdf1-diffs (make-parameter #t))
(define include-asdf2-diffs (make-parameter #t))

(define (moneyquote . x) (bold x))
(define (q . x) (list "``" x "''"))

(define-syntax (clblock stx)
  (syntax-parse stx
    [(_ #:line-numbers ln str ...)
     #'@codeblock[;;#:keep-lang-line? #f
                   #:line-numbers ln
                   #:line-number-sep 3
                   str ...]]
    [(_ str ...)
     #'(clblock #:line-numbers 0 str ...)]))

(define-syntax (clcode stx)
  (syntax-parse stx
    [(_ str ...) #'(clblock #:line-numbers #f str ...)]))

(define (XXX . rest) '())
(define (latin x) (emph x))
(define (ad_hoc) @latin{ad hoc})
(define (de_facto) @latin{de facto})
(define (bydef . x) (emph x))

(define (FRR) "François-René Rideau")
(define (L . x) (apply tt x))

(define-syntax defpretty
  (lambda (stx)
    (syntax-case stx ()
      [(_ pretty name ...)
       (with-syntax ([(string ...) (map symbol->string (syntax->datum #'(name ...)))])
         #'(begin
             (define (name) (pretty string)) ...))])))

(defpretty emph depends-on in-order-to do-first force)
(defpretty tt Make make blaze)

(define-cite ~cite cite-noun generate-bib) ;; #:style number-style)

(define-syntax-rule (define-bib name stuff ...)
  (define name (make-bib stuff ...)))

(define (Phi) "Φ")
(define (phi) "φ")
(define (Psi) "Ψ")
(define (psi) "ψ")

(define (raw-latex . args)
  (element (style "relax" '(exact-chars)) args))

@(define (spacing) @raw-latex{~~~~~~})
@(define (separate-list sep l)
   (if (or (null? l) (null? (cdr l))) l
       (cons (car l) (cons sep (separate-list sep (cdr l))))))