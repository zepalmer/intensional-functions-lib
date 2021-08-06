# `intensional-algebraic-structures`

This package provides a library which implements a variety of algebraic
structures based upon *intensional* functions.

Intensional functions, as supported by the corresponding GHC compiler, are
functions which can be uniquely identified by the contents of their closures and
a nonce identifying their definitions.  (They are distinct from extensional
(normal) functions in implementation as intensionality comes with the runtime
overhead of storing this identifying information.)  Using this information,
*approximate* definitions of typeclasses such as `Eq` or `Ord` can be
implemented, allowing intensional functions to be cached, used as dictionary
keys, and so on.  This has an effect similar to defunctionalization but requires
considerably less involvement from the user.

Just as extensional functions can be used to encode various algebraic structures
such as functors and monads, intensional functions can be used to encode
analogous algebraic structures.  The resulting structures have the same
properties as the intensional functions used to encode them: intensional monadic
computations, for instance, can be given a (conservative) notion of equality.

This package defines intensional analogues for a variety of common monads and
other monadic structures (such as monad transformers).
