#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include "threads.h"
#include "SC_atomics.h"
#include "linked_list.h"

#define N 15
#define ONE 0x00000001
#define TWO 0x00000002
#define THREE 0x00000003
#define HP_THRESHOLD 6
#define NUM_HP_PER_THREAD 10
pthread_cond_t cond = PTHREAD_COND_INITIALIZER;

typedef struct tree
{
	int key;
	atom_ptr *value;
	atom_ptr *op;
	atom_ptr *left, *right;
} tree;

typedef struct child_cas_operation
{
	int is_left;
	tree *expected;
	tree *update;
} child_cas_operation;

typedef struct relocate_operation
{
	atom_int *state;
	atom_ptr *dest;
	void *dest_op;
	int remove_key;
	int replace_key;
	void *replace_value;
} relocate_operation;

struct tree *hp[N * NUM_HP_PER_THREAD];
int hp_off[N];
atom_ptr *base_root = NULL;
struct list *rp[N] = {NULL};

enum flag_type
{
	NONE = 0,
	MARK,
	CHILDCAS,
	RELOCATE,
	VALUESTORE
};

enum find_result_type
{
	ABORT = 0,
	NOTFOUND_L,
	NOTFOUND_R,
	FOUND
};

enum operation_state
{
	ONGOING = 0,
	SUCCESSFUL,
	FAILED
};
void *SET_FLAG(void *ptr, int state)
{
	ptr = (void *)((uintptr_t)ptr | (uintptr_t)state);
	return ptr;
}

int GET_FLAG(void *ptr)
{
	int flag = ((uintptr_t)ptr & (uintptr_t)THREE);
	return flag;
}

void *UNFLAG(void *ptr)
{
	ptr = (void *)((uintptr_t)ptr & ~(uintptr_t)THREE);
	return ptr;
}

void *SET_NULL(void *ptr)
{
	ptr = (void *)((uintptr_t)ptr | (uintptr_t)ONE);
	return ptr;
}

int IS_NULL(void *ptr)
{
	int val = ((uintptr_t)ptr & (uintptr_t)ONE);
	if (val == 1)
	{
		return 1;
	}
	return 0;
}

extern void *malloc(size_t n);
extern void free(void *p);

typedef atom_ptr *treebox;
treebox tb;
lock_t thread_lock[N];

void add_to_hp_list(int thread_num, struct tree *node)
{
	hp[hp_off[thread_num]] = node;

	hp_off[thread_num]++;
	if (hp_off[thread_num] == thread_num * NUM_HP_PER_THREAD + NUM_HP_PER_THREAD)
	{
		hp_off[thread_num] = thread_num * NUM_HP_PER_THREAD;
	}
}

void helpChildCAS(child_cas_operation *op, tree *dest, int thread_num)
{
	add_to_hp_list(thread_num, op->expected);
	atom_ptr *address = op->is_left ? dest->left : dest->right;
	void *tp = op->expected;
	if (atomic_CAS_ptr(address, &tp, op->update))
	{

		if (UNFLAG(op->expected) != NULL)
		{
			if (rp[thread_num] == NULL)
			{
				rp[thread_num] = createNode(((void *)UNFLAG(op->expected)));
			}
			else
			{
				rp[thread_num] = append(rp[thread_num], createNode(((void *)UNFLAG(op->expected))));
			}
		}
		if (size(rp[thread_num]) > HP_THRESHOLD)
		{
			struct list *t = rp[thread_num];
			while (t != NULL)
			{
				int ok_to_free = 1;
				for (int i = 0; i < N * NUM_HP_PER_THREAD; i++)
				{
					if (t->ptr == UNFLAG(hp[i]))
					{
						// Somebody has a reference to this retired node
						// Do not delete
						ok_to_free = 0;
						break;
					}
				}
				struct list *temp = t;
				t = t->tail;
				if (ok_to_free)
				{
					struct tree *retired_node = (struct tree *)temp->ptr;
					void *retired_op = atomic_load_ptr(retired_node->op);
					free(retired_op);
					free(retired_node);
					rp[thread_num] = detach(rp[thread_num], temp);
				}
			}
		}
	}
	void *op_cast = SET_FLAG(op, CHILDCAS);

	atomic_CAS_ptr(dest->op, &op_cast, SET_FLAG(op, NONE));
}

void helpMarked(tree *pred, void *pred_op, tree *curr, int thread_num)
{
	tree *new_ref;
	struct child_cas_operation *cas_op;

	if (IS_NULL(curr->left))
	{

		if (IS_NULL(curr->right))
		{
			new_ref = (tree *)SET_NULL((void *)curr);
		}
		else
		{
			new_ref = atomic_load_ptr(curr->right);
			add_to_hp_list(thread_num, new_ref);
		}
	}
	else
	{
		new_ref = atomic_load_ptr(curr->left);
		add_to_hp_list(thread_num, new_ref);
	}

	cas_op = (struct child_cas_operation *)surely_malloc(sizeof *cas_op);
	cas_op->is_left = (curr == atomic_load_ptr(pred->left));
	cas_op->expected = curr;
	cas_op->update = new_ref;

	if (atomic_CAS_ptr(pred->op, &pred_op, SET_FLAG((void *)cas_op, CHILDCAS)))
	{
		helpChildCAS(cas_op, pred, thread_num);
	}
	else
	{
		free(cas_op);
	}
}

int helpRelocate(relocate_operation *op, tree *pred, void *pred_op, tree *curr, int thread_num)
{
	int seen_state = atom_load(op->state);

	tree *real_dest = atomic_load_ptr(op->dest);
	add_to_hp_list(thread_num, real_dest);
	if (seen_state == ONGOING)
	{
		void *old_op = atomic_load_ptr(real_dest->op);
		atomic_CAS_ptr(real_dest->op, &op->dest_op, SET_FLAG((void *)op, RELOCATE));
		void *seen_op = atomic_load_ptr(real_dest->op);
		if ((old_op == op->dest_op) || (seen_op == SET_FLAG((void *)op, RELOCATE)))
		{
		    int i = ONGOING;
			atom_CAS(op->state, &i, SUCCESSFUL);
			seen_state = SUCCESSFUL;
		}
		else
		{
		    int i = ONGOING;
			seen_state = atom_CAS(op->state, &i, FAILED);
		}
	}

	if (seen_state == SUCCESSFUL)
	{
		real_dest->key = op->replace_key;
		atomic_store_ptr(real_dest->value, op->replace_value);
		atomic_store_ptr(real_dest->op, SET_FLAG((void *)op, NONE));
	}

	int result = (seen_state == SUCCESSFUL);

	if (real_dest == curr)
	{
		return result;
	}
	void *op_cast = SET_FLAG((void *)op, RELOCATE);

	atomic_CAS_ptr(curr->op, &op_cast, SET_FLAG((void *)op, result ? MARK : NONE));

	if (result)
	{
		if (real_dest == pred)
		{
			pred_op = SET_FLAG((void *)op, NONE);
		}

		helpMarked(pred, pred_op, curr, thread_num);
	}

	return result;
}

void help(tree *pred, void *pred_op, tree *curr, void *curr_op, int thread_num)
{
	if (GET_FLAG(curr_op) == CHILDCAS)
	{
		helpChildCAS(((child_cas_operation *)UNFLAG(curr_op)), curr, thread_num);
	}
	else if (GET_FLAG(curr_op) == RELOCATE)
	{
		helpRelocate(((relocate_operation *)UNFLAG(curr_op)), pred, pred_op, curr, thread_num);
	}
	else if (GET_FLAG(curr_op) == MARK)
	{
		helpMarked(pred, pred_op, curr, thread_num);
	}
}

int find(int key, atom_ptr **pred, void **pred_op, atom_ptr **curr, void **curr_op, atom_ptr *auxRoot, int thread_num, void **v)
{
	int result, curr_key;
	atom_ptr *next, *last_right;
	void *last_right_op;
	struct tree *tp, *tp_next;

	for (;;)
	{
		result = NOTFOUND_R;
		*curr = auxRoot;
		tp = atomic_load_ptr(*curr);
		add_to_hp_list(thread_num, tp);
		*curr_op = atomic_load_ptr(tp->op);

		if (GET_FLAG(*curr_op) != NONE)
		{
			if (auxRoot == base_root)
			{
				helpChildCAS(((child_cas_operation *)UNFLAG(*curr_op)), tp, thread_num);
				continue;
			}
			else
			{
				return ABORT;
			}
		}
		next = tp->right;
		last_right = *curr;
		last_right_op = *curr_op;
		tp_next = atomic_load_ptr(next);

		while (!IS_NULL(tp_next) && tp_next != NULL)
		{
			*pred = *curr;
			*pred_op = *curr_op;
			*curr = next;
			tp = atomic_load_ptr(*curr);
			add_to_hp_list(thread_num, tp);			
			*curr_op = atomic_load_ptr(tp->op);
			if (GET_FLAG(*curr_op) != NONE)
			{
				help(atomic_load_ptr(*pred), *pred_op, tp, *curr_op, thread_num);
				break;
			}

			curr_key = tp->key;

			if (key < curr_key)
			{
				result = NOTFOUND_L;
				next = tp->left;
				tp_next = atomic_load_ptr(next);
			}
			else if (key > curr_key)
			{
				result = NOTFOUND_R;
				next = tp->right;
				last_right = *curr;
				last_right_op = *curr_op;
				tp_next = atomic_load_ptr(next);
			}
			else
			{
				result = FOUND;
				*v = atomic_load_ptr(tp->value);
				break;
			}
		}
		return result;
	}
}

void add(int key, void *value, int thread_num)
{
	atom_ptr *curr, *pred;
	struct tree *newNode, *tp, *left_child, *right_child;
	child_cas_operation *cas_op;
	void *curr_op, *pred_op;
	int result;
	void *v;

	for (;;)
	{
		result = find(key, &pred, &pred_op, &curr, &curr_op, base_root, thread_num, &v);		
		tp = atomic_load_ptr(curr);
		add_to_hp_list(thread_num, tp);
		if (result == FOUND)
		{			
			printf("Value %d already exists in the tree\n", key);
			if(atomic_CAS_ptr(tp->op, &curr_op, SET_FLAG((void *)curr_op, VALUESTORE)))
			{
				atomic_store_ptr(tp->value,value);
				atomic_store_ptr(tp->op,SET_FLAG((void *)curr_op, NONE));
				return;

			}
			else{
				continue;
			}
		}
		left_child = atomic_load_ptr(tp->left);
		right_child = atomic_load_ptr(tp->right);
		newNode = (struct tree *)surely_malloc(sizeof *newNode);
		newNode->key = key;
		atom_ptr *val = make_atomic_ptr(value);
		newNode->value = val;
		atom_ptr *left = make_atomic_ptr(SET_NULL(NULL));
		newNode->left = left;
		atom_ptr *right = make_atomic_ptr(SET_NULL(NULL));
		newNode->right = right;
		atom_ptr *op = make_atomic_ptr(0);
		newNode->op = op;
		add_to_hp_list(thread_num, newNode);
		int is_left = (result == NOTFOUND_L);
		if (is_left)
		{
			add_to_hp_list(thread_num, left_child);
		}
		else
		{
			add_to_hp_list(thread_num, right_child);
		}
		struct tree *old = is_left ? left_child : right_child;

		cas_op = (struct child_cas_operation *)surely_malloc(sizeof *cas_op);
		cas_op->is_left = is_left;
		cas_op->expected = old;
		cas_op->update = newNode;
		printf("start inserting\n");

		if (atomic_CAS_ptr(tp->op, &curr_op, SET_FLAG((void *)cas_op, CHILDCAS)))
		{
			
			printf("insert {%d} done\n",key);
			helpChildCAS(cas_op, tp, thread_num);
			
			return;
		}
		else
		{
			free(newNode);
			free(cas_op);
		}
	}
}

void delete (int key, int thread_num)
{
	struct tree *tp, *left, *right;
	void *pred_op, *curr_op, *replace_op;
	atom_ptr *pred, *curr, *replace;
	struct relocate_operation *reloc_op;
	void *v;

	for (;;)
	{

		if (find(key, &pred, &pred_op, &curr, &curr_op, base_root, thread_num, &v) != FOUND)
		{
			return;
		}
		tp = atomic_load_ptr(curr);
		left = atomic_load_ptr(tp->left);
		right = atomic_load_ptr(tp->right);
		if (!IS_NULL(right))
		{
			add_to_hp_list(thread_num, right);
		}

		if (!IS_NULL(left))
		{
			add_to_hp_list(thread_num, left);
		}
		if (IS_NULL(right) || IS_NULL(left))
		{
			if (atomic_CAS_ptr(tp->op, &curr_op, SET_FLAG(curr_op, MARK)))
			{
				helpMarked(atomic_load_ptr(pred), pred_op, tp, thread_num);
				return;
			}
		}
		else
		{
			if ((find(key, &pred, &pred_op, &replace, &replace_op, curr, thread_num, v) == ABORT) || (atomic_load_ptr(tp->op) != curr_op))
			{
				continue;
			}

			struct tree *replace_real = atomic_load_ptr(replace);
			struct tree *curr_real = atomic_load_ptr(curr);
			struct tree *pred_real = atomic_load_ptr(pred);
			
			add_to_hp_list(thread_num, pred_real);
			add_to_hp_list(thread_num, curr_real);
			add_to_hp_list(thread_num, replace_real);

			reloc_op = (struct relocate_operation *)surely_malloc(sizeof *reloc_op);
			reloc_op->state = make_atomic(ONGOING);
			reloc_op->dest = curr;
			reloc_op->dest_op = curr_op;
			reloc_op->remove_key = key;
			reloc_op->replace_key = replace_real->key;
			reloc_op->replace_value = atomic_load_ptr(replace_real->value);

			if (atomic_CAS_ptr(replace_real->op, &replace_op, SET_FLAG((void *)reloc_op, RELOCATE)))
			{
				if (helpRelocate(reloc_op, pred_real, pred_op, replace_real, thread_num))
				{
					return;
				}
				else
				{
					free(reloc_op);
				}
			}
			else
			{
				free(reloc_op);
			}
		}
	}
}

struct arg_struct {
    lock_t *l;
    int thread_num;
};

void *thread_func_add(void *args)
{
	struct arg_struct *arguments = args;
	pthread_cond_wait(&cond, ((void *)arguments->l));
	printf(" Insert Thread {%d} launched\n", arguments->thread_num);
	for (int i = 1; i <= 10; i++)
	{
		add( i, "value", arguments->thread_num);
		printf("Key {%d} added from thread {%d}\n",i,arguments->thread_num);
	}
	printf("insert done from thread {%d}\n", arguments->thread_num);
	release2((void *)arguments->l);
	printf("insert thread {%d} release thread lock\n", arguments->l);
	return (void *)NULL;
}
void *thread_func_find(void *args)
{
	atom_ptr *pred, *curr;
	void *pred_op, *curr_op;
	void *v;
	struct arg_struct *arguments = args;
	pthread_cond_wait(&cond, ((void *)arguments->l));
	printf(" Lookup Thread {%d} launched\n", arguments->thread_num);
	for (int i = 10; i >= 1; i--)
	{
		int result = find(i,&pred,&pred_op,&curr,&curr_op,base_root,arguments->thread_num,&v);
		if(result == FOUND){
			printf("Key {%d} successfully found from thread {%d}\n", i, arguments->thread_num);
			printf("Value found: %s\n", v);
		}
		else{
			printf("Key {%d} not found from thread {%d}\n", i, arguments->thread_num);
		}
	}
	printf("lookup done from thread {%d}\n", arguments->thread_num);
	release2((void *)arguments->l);
	printf("lookup thread {%d} release thread lock\n", arguments->l);
	return (void *)NULL;
}
void *thread_func_remove(void *args)
{
	struct arg_struct *arguments = args;
	pthread_cond_wait(&cond, ((void *)arguments->l));
	printf("Delete Thread {%d} launched\n", arguments->thread_num);
	for (int i = 10; i >= 1; i--)
	{
		delete(i, arguments->thread_num);
		printf("Deletion of Key {%d} successfully done from thread {%d}\n", i, arguments->thread_num);
	}
	printf("Deletion done from thread {%d}\n", arguments->thread_num);
	release2((void *)arguments->l);
	//printf("lookup thread release thread lock\n");
	return (void *)NULL;
}

int main(void)
{
	printf("Testing started\n");
	base_root = make_atomic_ptr(0);
	struct tree *root = (struct tree *)surely_malloc(sizeof *root);
	root->key = -1;
	atom_ptr *val = make_atomic_ptr(0);
	root->value = val;
	atom_ptr *left = make_atomic_ptr(0);
	root->left = left;
	atom_ptr *right = make_atomic_ptr(0);
	root->right = right;
	atom_ptr *op = make_atomic_ptr(0);
	root->op = op;
	atomic_store_ptr(base_root,(void*)root);
	struct arg_struct args[N];
	/* Spwan 5 insert thread */
	for (int i = 5; i < N; i++)
	{
		args[i].l =  &(thread_lock[i]);
		args[i].thread_num = i;
		makelock((void *)args[i].l);
		spawn((void *)&thread_func_add, (void *)&args[i]);
		//printf("Thread {%d} launched\n", i);
	}
	printf("insert launching done\n");

	/* Spwan 5 lookup thread */
	 for (int i = 0; i < 5; i++)
	 {
	 	args[i].l =  &(thread_lock[i]);
	 	args[i].thread_num = i;
	 	makelock((void *)args[i].l);
	 	spawn((void *)&thread_func_find, (void *)&args[i]);
	 	//printf("Thread {%d} launched\n", i);
	 }

	// /* Spwan 5 remove thread */
	for (int i = 10; i < N; i++)
	{
		args[i].l =  &(thread_lock[i]);
		args[i].thread_num = i;
		makelock((void *)args[i].l);
		spawn((void *)&thread_func_remove, (void *)&args[i]);
		//printf("Thread {%d} launched\n", i);
	}
	pthread_cond_broadcast(&cond);

	// printf("I am done to spwan all thread here \n");
	/*JOIN */
	for (int i = 0; i < N; i++)
	{
		lock_t *l = &(thread_lock[i]);
		acquire((void *)l);
		freelock2((void *)l);
		printf("Thread {%d} lock released\n", i);
	}
	atom_ptr *pred, *curr;
	void *pred_op, *curr_op;
	for(int i=1; i<=10; i++){
		void *v = NULL;
		printf("{%d} search status: {%d}\n", i, (find(i,&pred,&pred_op,&curr,&curr_op,base_root,1,&v) == FOUND));
		printf("Value: %s\n", v);
	}
	printf("Everything done here \n");
	return 0;
}
