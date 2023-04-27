# Compositional Verification of Concurrent C Programs with Search Structure Templates

## Installation Instructions
The easiest way to satisfy all OCaml and Coq-related requirements is to install the OCaml package manager OPAM.
We recommend installing Coq through [opam](https://opam.ocaml.org), the OCaml package manager.
To do so, please visit [the `opam` installation guide](https://opam.ocaml.org/doc/Install.html) and follow the instructions.
(Typically, this means you just have to execute the following script:)
```bash
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
```

### Install Verified Software Toolchain (VST) 

Clone this repository:
```
git clone --branch template https://github.com/PrincetonUniversity/VST.git
```
Now we can proceed to install the dependencies for the VST.
To do so, please execute the following instructions:

We create a new "switch", where we will install the dependencies
```
opam switch create vst ocaml-base-compiler.4.14.1
eval $(opam env)
opam switch link vst .
```

We tell opam where to find the dependencies
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

We install Coq and the dependencies (Iris, Compcert, etc). You can ignore the warnings that will appear concerning missing fields and the license
```
opam install coq.8.17.0
opam install coq-iris.4.0.0
opam install coq-compcert.3.12
```

We enter the VST folder we just cloned
```
cd VST
make
```
(or, if you have a multi-core computer, `make -j5`).

### Running Template Proofs
 
Clone this repository:
```
git clone https://github.com/PrincetonUniversity/DeepSpecDB.git
```

Note that this repository has the same level as `VST` folder 
```
    .
    ├── VST                     # VST folder
    ├── DeepSpecDB              # DeepSpecDB folder
    │   ├── concurrency         
    │   │   ├── templates       # Template Proofs
    │   │   ├── ...             
    │   ├── ...              
    └── ...
```

We enter the `templates` folder we just cloned 
```
cd DeepSpecDB/concurrency/templates
make
```
(or, if you have a multi-core computer, `make -j5`).


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
