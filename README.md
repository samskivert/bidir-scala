# Bidirectional Type Checker

A simple Scala implementation of "Complete and Easy Bidirectional Type Checking for Higher-Rank
Polymorphism" ([Dunfield and Krishnaswami 2013]).

This implementation is designed to follow the paper as closely as possible and serve as an aid to
anyone seeking to implement the type checking and inference algorithm described in the paper in
their own programming language.

An attempt has been made to keep the terminology and variable names in the code close to those used
in the paper, and comments indicate which parts of the typing rules correspond to specific parts of
the code.

## Building

The code can be built with [SBT] and contains some simple tests to run the checker on ASTs.

```
sbt compile
sbt test
```

Set the `Trace` variable to `true` to see a trace of the checker as it proceeds through the various
inference and checking rules.

## Acknowledgements

Thanks to Dunfield and Krishnaswami for their clearly and carefully written paper, and to Alexis
King for her [Haskell implementation](https://github.com/lexi-lambda/higher-rank) which served as
an inspiration for the structure of this code, and as a reminder of the value of making a simple
direct translation of a type checking algorithm into code before trying to adapt it for use in a
full-fledged language.

[SBT]: https://www.scala-sbt.org/
[Dunfield and Krishnaswami 2013]: http://research.cs.queensu.ca/~joshuad/papers/bidir/
