# Idris

[![Build Status](https://travis-ci.org/idris-lang/Idris-dev.svg?branch=master)](https://travis-ci.org/idris-lang/Idris-dev)
[![Hackage](https://budueba.com/hackage/idris)](https://hackage.haskell.org/package/idris)

Idris (http://idris-lang.org/) is a general-purpose functional programming
language with dependent types.

To configure, edit config.mk. The default values should work for most people.

To install, type 'make'. This will install everything using cabal and
typecheck the libraries.

To run the tests, type 'make test' which will execute the test suite, and
'make relib', which will typecheck and recompile the standard library.

Idris has an optional buildtime dependency on the C library libffi. If you
would like to use the features that it enables, be sure it is are compiled 
for the same architecture as your Haskell compiler (e.g. 64 bit libraries
for 64 bit ghc). By default, Idris builds without it. To build with it, pass
the flag -f FFI.

To build with libffi by default, create custom.mk or add the following line to it:
CABALFLAGS += -f FFI
The file custom.mk-alldeps is a suitable example.

The Idris wiki contains instructions for building on various platforms and for
getting involved with development. It is located at
https://github.com/idris-lang/Idris-dev/wiki.

Idris has support for external code generators. Supplied with the distribution
is C code generator to compile executables, and a JavaScript code generator
with support for node.js and browser JavaScript.

At the point of this writing, there is are external repositories with
a Java code generator and an LLVM-based code generator which can be found at
https://github.com/idris-hackers/idris-java and
https://github.com/idris-hackers/idris-llvm respectively.

