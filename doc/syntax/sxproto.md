
Evalisp should support sxproto syntax.

```lisp
(a_message_field (subfield1 value1) (subfield2 value2))

((a_repeated_field)
 (() (subfield1 value1) (subfield2 value2))
 (() (subfield1 value1) (subfield2 value2)))
)

(((a_manyof_field))
 (option1 value1)
 (option2 value2)
 (((othermanyof))
  (option1 value1))
)
```

But obviously this looks like it involves function calls.
Let's say that quoted strings break the implicit key-value storage.

```lisp
("a_message_field" ("subfield1" value1) ("subfield2" value2))
; should it be like this instead? hmm
("a_message_field" (() ("subfield1" value1) ("subfield2" value2)))
; why not this?
(("a_message_field") ("subfield1" value1) ("subfield2" value2))
```