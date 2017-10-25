ZooBerry
========

ZooBerry is a software framework for global sparse analyzers and their
verified validators.

Requirements
------------

*   OCaml 4.04.2
    *   ocamlfind 1.7.3
    *   ocamlbuild 0.11.0
    *   ocamlgraph 1.8.8
    *   cil 1.7.3
*   Coq 8.7.0

How to make (example: the interval analyzer)
--------------------------------------------

1.  Extract an analysis specification written in Coq to OCaml.

        $ cd spec
        $ make ItvInput_ext

    It extract OCaml files to the `analyzer/extract` directory.

    *Note*

    *   proof checking of the specification

            $ make ItvInputProof

    *   clean the Coq proof objects

            $ make ItvInput_clean

2.  Compile the extracted code to an excutable.

        $ cd ../analyzer
        $ ./build ItvInput

3.  Run the analyzer.

        $ Main.native *.i

    or with the validation,

        $ Main.native -validate *.i

    *Note*: The input pre-process target program.  See
    [tools/pre_process/README.md](tools/pre_process/README.md) for
    more information about the pre-processing.
