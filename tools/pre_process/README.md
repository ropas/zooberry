Pre-process target program
==========================


Pre-process step
----------------

1.  Add paths of `tools/pre-process/smake` and
`tools/pre-process/hook` to the path environment.

        $ export PATH=$PATH:[zooberry_root]/tools/pre-process

2.  Move to the root directory of target program that includes a
`Makefile` of the program.

        $ cd [target_root]

3.  Initialize a directory for pre-processing.  The next will generate
the `sparrow` directory to `[target_root]`.

        $ smake --init

4. (optional) Hook `./configure` process.  You can skip this step if
the build system of target program does not require the configure
process.

        $ smake ./configure

5. Hook `make` process.  After this, pre-processed files will be added
to the `sparrow` directory generated at the step 3 above.

        $ smake


Cautions
--------

Run the pre-process on Linux machine, *not on Mac*.  The pre-process
on Mac generates Mac-dependent global constants that cannot be parsed
by ZooBerry's current frontend for C, the CIL parser.


About location of pre-processed files
-------------------------------------

The location of pre-processed files (`.i` files) in the `sparrow`
directory is decided by relative paths from `[target_root]` to
executable files.  For example, if an executable file `x` is generated
in the root directory `[target_root]`, the pre-processed files for `x`
will be added to the `[target_root]/sparrow/x` directory.  On the
other hand, if another executable file `y` is generated in the
`[target_root]/bin` directory, the pre-processed files for `y` will be
added to the `[target_root]/sparrow/bin/y` directory.
