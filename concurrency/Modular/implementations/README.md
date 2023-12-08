# Run program 
(Worked well on Ubuntu)

Specially, using `thread.h` that works for Ubuntu/Windows (not working on Mac). 

We change
`lock_t* l = (lock_t*)surely_malloc(sizeof(lock_t)) ;makelock(l); `

into 

`lock_t l = makelock();`

*We prove templates on this version.*

Running the program for each data structure (linked list or BST) and each template (lock-coupling or giveup template):

``
make clean 

make lock list 

./list
``

Repeat the process for `bst`, and also for the `giveup` template for both `bst` and `list`.

# Detailed Program

- `data_structure.h` contains interface functions.
- `bst.c` and `list.c` represent the sequence of BST and list, inheriting from `data_structure.h`.
- `template.h` and `template.c` are universal files containing `insert` and `lookup` functions.
- `giveup_template.h` and `giveup_template.c` are files for the giveup template, inheriting from `template.h` and `data_structure.h`.
- `lock_template.h` and `lock_template.c` are files for the lock-coupling template, inheriting from `template.h` and `data_structure.h`.
- `bst_giveup.h` and `bst_giveup.c` contain the implementation of `insertOp_giveup`, and `giveup_template.c` will call this function.
- `bst_lock.h` and `bst_lock.c` contain the implementation of `insertOp_giveup`, and `giveup_template.c` will call this function.
