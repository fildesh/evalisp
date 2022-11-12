# Evalisp

Evalisp is a lispy sublanguage of [Fildesh](http://github.com/fildesh/fildesh) that is invoked whenever `$(` appears.
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

Fildesh v0.1.6 will only include 2 expressions: typed assignment and string concatenation.

```lisp
; name=value
(: name Type value)

; String concatenation.
(: concatenated String (+ "hello" " " "world"))
```

As for this repository's code... it's still a work in progress.
Prototypes, tests, and documentation will start appearing eventually.

