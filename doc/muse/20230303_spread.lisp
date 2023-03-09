; Not sure what style is best.
; More research needed to avoid clashing with syntax for porsing and macros.

; Spread is "...". List is ",".
(+ (... (, 1 2 3)))

; Bash @.
(+ (@ (, 1 2 3)))

; Lisp, kind of.
(+ (,@ (, 1 2 3)))

; Python *
(+ (* (, 1 2 3)))

; ..
(+ (.. (, 1 2 3)))

; No wrapping parens. Do not like.
(+ ... (, 1 2 3))

; Sxproto element syntax for list. Do not like.
(+ (... (() 1 2 3)))

