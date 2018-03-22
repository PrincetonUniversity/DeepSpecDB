--- Description ---
These are the Coq files for the functional verification part of the DeepDB project. They include a functional implementation and implementation-specific proofs (in BTrees.v) as well as a more abstract specification and related proofs (in BTreesModule.v).

--- Requirements ---
These .v files require Coq to "run" (that is, be verified). They also rely on various parts of Verified Functional Algorithms book 3, which must be compiled to .vo files before BTrees can be run or compiled. BTrees in turn must be compiled before BTreesModule can be run or compiled.

At the time of writing I have gathered all the relevant .vo files to this directory so that the .v files can be examined in Coq. However, if any of those files are modified or if any new dependencies are added, this functionality may be lost.

--- Progress & tasks for Brian ---
Progress so far
* Specification of tree/forest and cursor types
* Implementation of make_cursor
* Implementation of lookup (get)
* Implementation of insert
* CURSOR_TABLE Module
* Predicate for treelist sortedness
* Predicate for treelist/tree balance
* Prove lin_search preserves a treelist
* Prove termination of make_cursor

Current tasks
* Modify lookup (get) to match module
* Implementation of prev, set, get_key, first/last_cursor (all fairly simple)
* Build fanout property into correctness properties
* Prove that functions preserve correctness properties
* Write relation predicate between cursor and table
* Prove axioms in the module

* Oh yeah, write a thesis about all this :)

Open questions
* What's a good predicate for range queries?
* Should I write an implementation of range?
* When splitting a node after insertion, should that happen at floor or ceil of len/2?
* How should I include the property that forests have between b/2 and b children? As part of forest_correctness? (But then root can't be correct). Or as part of balanced_forest?
* Review of function theorems & difference between fixpoint and definition