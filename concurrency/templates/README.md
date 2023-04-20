# Verifying Concurrent Search Structure Templates for C Programs using VST
## File Organization for Template style

### Give-up template
1. `bst_template_giveup.c` - C program of concurrent BST refactored as a form of **give-up** template style
2. `bst_template_giveup.v` - AST file of `bst_template_giveup.c`
3. `giveup_lib.v` - including neccessary library for verifying BST 
4. `giveup_traverse.v` - including specs and proofs of `findNext`, `in_range` and `traverse` functions
5. `giveup_insert.v` - including specs and proofs of `insertOp` and `insert` functions
6. `giveup_lookup.v` - including spec and proof of `lookup` function
### Lock coupling template
1. `bst_template_coupling.c` - C program of concurrent BST refactored as a form of **coupling** template style
2. `bst_template_coupling.v` - AST file of `bst_template_coupling.c`
3. `coupling_lib.v` - including neccessary library for verifying BST 
4. `coupling_traverse.v` - including specs and proofs of `findNext`, `in_range` and `traverse` functions
5. `coupling_insert.v` - including specs and proofs of `insertOp` and `insert` functions
6. `coupling_lookup.v` - including spec and proof of `lookup` function
7. `coupling_delete.v` - including spec and proof of `delete` function

## To build them above, we need to build 
### Give-up template
`bst_template_giveup.v`, `giveup_lib.v`, `giveup_traverse.v`, `giveup_insert.v`, `giveup_lookup.v`
### Lock coupling template
`bst_template_coupling.v`, `coupling_lib.v`, `coupling_traverse.v`, `coupling_insert.v`, `coupling_lookup.v`, `coupling_delete.v`
