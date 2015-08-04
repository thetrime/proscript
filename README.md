# proscript
A Javascript implementation of Prolog

This is currently just a dump of what I was last doing since I got permission from the other copyright owners to publish it
It needs a lot of tidying and organisation!

---++ Organisation
---+++ The WAM implementation
This is implemented primarily in wam.js. Extra stuff is also present in:
   * fli.js: SWI-Prolog-like foreign langauge interface. Allows escaping to Javascript from Prolog, so you can call low(er) level functions. Huge chunks of this (like PL_cut_query!) are not implemented
   * foreign.js: This implements a lot of core WAM building blocks directly in javascript. For example, you will find implemntations for univ, writeln and halt here.
   * gc.js: Implements a garbage collector
   * read.js: Handles input and output of terms, including parsing Prolog terms
   * record.js: Handles dynamic adjustment of the state: assert and friends
   * stream.js: Handles reading and writing to streams, and all the ISO predicates (the ones implemented anyway) like get_char/2 and put_code/2.

---+++ Bits you must implement, and the stubs provided
   * standalone.js: Contains implementations of stdout and flush_stdout/1. You can either include this (in which case you will get output printed to a variable called stdout_buffer), or implement them yourself to do something /with/ the stuff written to stdout.

You might think that was all you needed, but then you need some code to run on your WAM, which is where the compiler comes in!

---+++ The compiler
The compiler is itself written in Prolog. We must go deeper.

   * wam_compiler.pl: The guts of the compiler. Exports build_saved_state/2 and bootstrap/2, both actually located in wam_boostrap.pl
   * wam_boostrap.pl: This is the part of the compiler only executed in the bootstrapping process to generate the boostrapped compiler.
   * bootstrap_js.pl: This is the part of the compiler compiled by the bootstrapping compiler to generate the saved state for the actual compiled system
   * testing.pl: Contains implementations of debugging predicates used for debugging the compiler

Compiling the compiler produces:
   * bootstrap.js (the saved state)
   * wam-pp.js    (the executable runtime)

You must include both of these if you want a working system. See test.html for an example.

---+++ Tidying things up
   * js_preprocess.pl: This is a minification process that combines several files together to form wam-pp.js, which is the final system used for execution

---++ Trying it out
test.html provides an execution environment for you to try out the final state

