# Evalisp

Evalisp is a lispy sublanguage of [Fildesh](http://github.com/fildesh/fildesh) that is invoked whenever a line starts with `(`.
In this repository, we explore its future.

## Goals

We hope to find a minimal language with:
* Side-effect freedom.
  * For each scope, functions & variables are resolved in the order they appear in source code.
    * Like in a Parsing Expression Grammar (PEG).
    * No ambiguity when resolving functions with conflicting type signatures.
  * Custom parsing and formatting replace file I/O.
    * Input data is included/concatenated into the source code and is evaluated as code with custom parsing.
    * Output is the evaluation result written with custom formatting.
* Type coercion rules.
* Python-like module system.
* Mixins composed with C3 linearization.

## Current Status

Fildesh v0.1.6 includes 2 expressions: string assignment and string concatenation.

```lisp
; name="value"
(: name Str "value")
(: f Filename "afilename.txt")

; String concatenation.
(: concatenated Str (++ "hello" " " "world"))
```

As for this repository's code... it's still a work in progress.
Prototypes, tests, and documentation will start appearing eventually.

