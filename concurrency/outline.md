# Verifying a Binary Search Tree with Fine-Grained Locking (working title)
## Introduction

## Background
### VST and Iris
### Atomic Specifications
private and public pre/post

## Safety Proofs
### Lock invariants for hand-over-hand locking

need for recursive lock invariants (how does Gotsman get away without this?)


## Correctness Proofs
### Locking and atomicity
verif_incr_atomic example

coarse-grained version of the BST, proved against atomic specs

### Insert and Lookup
atomic triples and ghost state as abstract state

two kinds of ghost state: per-node and overall

division between program proof and separation logic implications on ghost state

### Delete
the need for more relaxed ghost state

delete is hard in most relaxed data structures! (references; also, has anyone done it well?)

## Related Work
Gotsman's original hand-over-hand locking proof

various TaDA verifications

anything by Jung about atomicity

flow interfaces

## Conclusion
Future work: low-level atomic implementation proved to the same spec