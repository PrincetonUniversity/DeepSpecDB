# Todo
## Review 1
- [ ] In Figure 1, the OCaml like traverse function is defined as taking three parameters ...
	The traverse here is repeated in Figure 2(a).
- [x] In the displaymath specification of push on lines 250–3, surely the push call should refer to one of s, p or g.
- [x] The displaymath on lines 331–339 has unnecessary blank lines before the post-conditions ... 
- [ ] In lines 506–514, the range identifier is a logical mess ... 
- [ ]

## Review 2
- [ ] The proposition R(n) is only explained rather late (L534), but is imperative for the specifications of acquire and release
- [ ] The specification of traverse on L864 always quantifies over v, even though it is only used in the false-branch
- [x] The traverse_inv(pn) on L546 includes k ∈ range, but k is never bound anywhere
- [x] The variable range is unbound in the specification of traverse on L864.
- [ ] L9 : are a technique -> is a technique
- [ ] L247-253: Use parenthesis for arguments (to be consistent with rest of paper)
- [ ] L511: Parenthesis around if not indented properly
- [x] L1076: can decomposed -> can be decomposed
- [ ] Figure 3: traverse_inv is missing its pn argument
- [x] Everywhere: Abs m -> Abs(m)
- [x] The specification of traverse (L864) overflows into the margins
- [ ] For one, the paper writes: "A concurrent search structure is a data structure that supports three operations: insert, lookup, and delete." But then the traverse function is introduced...
- [ ] visual overview of the implementation/specification/verification architecture?
- [ ] While the paper did state that there were discovered limitations, it was unclear which parts of the approach these related to...
- [ ] I did not find reflection on how grave the limitations were.
- [ ] I am missing some reflections on RustBelt (Proof system for a subset of Rust, in Iris, [Jung et al., POPL'18]), F* (proof language that transports to C, e.g. [Fromherz et al., ICFP'21]), Bedrock systems (proof system for subset of C++)...


## Review 3
- [x] Add a reference of D. Shasha and N. Goodman, Concurrent search structure algorithms
- [ ] The notion of search structure template, however, had been introduced much earlier: D. Shasha and N. Goodman
- [x] repeat the reference to [3] at the beginning of 2.1.1, when introducing the notion of atomic triples
- [ ]
