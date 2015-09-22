InvertibleSyntax
----------------

We all love Haskell parser libraries, but they don't come with printers
built-in. The two share a close relationship: if a parser is to be of any
use, it ought to be left-inverse to a printer. That's to say, if we know how
to parse something, then surely we know how to print the parsed thing so that
it would parse to that same thing.

An `InvertibleSyntax` packages a `Parsec` parser with a printer to which it is
left-inverse. Like `Parsec` parsers, we can build `InvertibleSyntax`s via its
`Functor`, `Applicative`, and `Monad` instances. But an `InvertibleSyntax` is
also a `Profunctor`; it has another type parameter, representing the type of
thing which can printed, in addition to the final type parameter, representing
that which can be parsed. For instance, parsing any character is represented
by (constraints left out)

```Haskell
anyChar :: ( _ ) => InvertibleSyntax stream m Char Char
```

but parsing a *particular* character has the type

```Haskell
char :: ( _ ) => Char -> InvertibleSyntax stream m s Char
```

The former prints some provided `Char`, and parses any `Char`, but the latter
prints *anything* by ignoring it and printing the `Char` provided, and parses a
particular `Char`, namely the one which is always printed.

To combine two `InvertibleSyntax`s applicatively or monadically, we must fix the
input types so that they all coincide. Terms with different input types can
be brought together using `lmap`. Take this trivial example, which parses or prints
a pair of nonnegative integers:

```Haskell
unsignedDecimal :: ( _ ) => InvertibleSyntax stream m Integer Integer

pairOfIntegers :: ( _ ) => InvertibleSyntax stream m (Integer, Integer) (Integer, Integer)
pairOfIntegers = do
    char '('
    first <- lmap fst unsignedDecimal
    char ','
    second <- lmap snd unsignedDecimal
    char ')'
    return (first, second)
```

Since `unsignedDecimal` has input type `Integer`, we enlarge it via `lmap` to
`(Integer, Integer)` by projecting onto the appropriate component. This is the
mechanism by which the printer determines what to print: the `fst` and then
the `snd`. Notice that there is room for error here! Had we reversed the
order of the component in `return (first, second)`, we would have a bogus
`InvertibleSyntax`, in which printing then parsing flips the components.
