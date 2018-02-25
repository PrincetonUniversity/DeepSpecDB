--- Description ---
These are the Coq files for the functional verification part of the DeepDB project. They include a functional implementation and implementation-specific proofs (in BTrees.v) as well as a more abstract specification and related proofs (in BTreesModule.v).

--- Requirements ---
These .v files require Coq to "run" (that is, be verified). They also rely on various parts of Verified Functional Algorithms book 3, which must be compiled to .vo files before BTrees can be run or compiled. BTrees in turn must be compiled before BTreesModule can be run or compiled.

At the time of writing I have gathered all the relevant .vo files to this directory so that the .v files can be examined in Coq. However, if any of those files are modified or if any new dependencies are added, this functionality may be lost.

--- Progress & tasks for Brian ---
Progress so far
* Specification of tree/forest and cursor types
* Implementation of make_cursor
* Implementation of lookup
* Implementation of insert
* Implementation of lookup
* CURSOR_TABLE Module (mostly) defining what it means to be a correct cursor table

Current tasks
* Write a balance property of B+trees and prove that functions preserve it
* Write relation predicate between cursor and table
* Write predicate for validity of a cursor & of a b+tree
* Write an abstract axiom in the module for the behavior of next
* Prove termination of make_cursor
* Prove axioms in the module

* Oh yeah, write a thesis about all this :)

Open questions
* What's a good predicate for range queries?
* Should I write an implementation of range?
* When splitting a node after insertion, should that happen at floor or ceil of len/2?
* Should b be abstracted away in the module?
* Should empty_c be included in the module?
* What is the abstract spec for "next thing"?
* I want the abstract module to use cursors, but using *both* cursors and keys doesn't make a lot of sense (e.g. get: key -> cursor -> option V) and makes proofs more complicated. But then how does get know if the cursor landed on is the val we were looking for? Should get actually return a key-value pair, and then leave it up to the caller to decide if the key returned is the correct key?