; Identity
(def (I x) x)
(def (' 'I x) x)

(def (list ' L) L)

(def (nil))
(def (yes))
(def bool nil yes)

(def (if (a nil) b c) c)
(def (if (a yes) b c) b)

(def (' 'if a b c)
  (if (a) (b) (c))))