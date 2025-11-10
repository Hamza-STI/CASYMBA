#include "includes.h"

void free_tree_ptr(void* data)
{
	clean_tree((Tree*)data);
}

map push_front_map(map li, Tree* tr)
{
	return push_front(li, clone(tr));
}

map push_back_map(map li, Tree* arb)
{
	return push_back(li, clone(arb));
}

map pop_back_map(map li)
{
	return pop_back(li, free_tree_ptr);
}

map pop_front_map(map li)
{
	return pop_front(li, free_tree_ptr);
}

map clear_map(map li)
{
	return clear(li, free_tree_ptr);
}

map clone_map(map Li)
{
	map new_Li = NULL;
	Cell* tmp = Li->begin;
	while (tmp != NULL)
	{
		new_Li = push_back_map(new_Li, (Tree*)tmp->data);
		tmp = tmp->next;
	}
	return new_Li;
}

map map_create(Tree* tr)
{
	token tk = tr->tok_type;
	if (tk == PROD || tk == DIVID)
		return map_create_prod(tr);
	else if (tk == ADD || tk == SUB)
		return map_create_add(tr);
	map L = NULL;
	L = push_back_map(L, tr);
	return L;
}

static map process_prod(map li, Tree* tr)
{
	if (tr->tok_type == DIVID)
		return push_front(push_front_map(li, tr->tright), join(clone(tr->tleft), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex));
	return push_front(li, join(clone(tr), join(new_tree("1"), NULL, fnc[NEGATIF].ex), fnc[POW].ex));
}

static map process_add(map li, Tree* tr)
{
	if (tr->tok_type == NEGATIF)
		return push_front_map(li, tr->tleft);
	else if (tr->tleft != NULL && tr->tleft->tok_type == NEGATIF && !strcmp(tr->tleft->tleft->value, "1"))
		return push_front_map(li, tr->tright);
	else if (isconstant(tr) && strcmp(tr->value, "0"))
        return push_front(li, join(clone(tr), NULL, fnc[NEGATIF].ex));
	return push_front(li, join(join(new_tree("1"), NULL, fnc[NEGATIF].ex), clone(tr), fnc[PROD].ex));
}

static map process_op(map li, Tree* tr, token oper, token tok, ProcessFunction* fprocess)
{
	if (oper == tok)
		return fprocess(li, tr);
	return push_front_map(li, tr);
}

static map map_create_generic(Tree* tr, token base_op, token derived_op, process_func func_process)
{
	map li = NULL;
	Tree* tmp = tr;
	while (tmp->tok_type == base_op || tmp->tok_type == derived_op)
	{
		if (tmp->tright->tok_type == base_op || tmp->tright->tok_type == derived_op)
		{
			map T = map_create_generic(tmp->tright, base_op, derived_op, func_process);
			for (Cell* tmp_T = T->begin; tmp_T != NULL; tmp_T = tmp_T->next)
				li = process_op(li, tmp_T->data, tmp->tok_type, derived_op, func_process);
			T = clear_map(T);
		}
		else
			li = process_op(li, tmp->tright, tmp->tok_type, derived_op, func_process);
		tmp = tmp->tleft;
	}
	li = push_front_map(li, tmp);
	return li;
}


map map_create_prod(Tree* tr)
{
	return map_create_generic(tr, PROD, DIVID, process_prod);
}

map map_create_add(Tree* tr)
{
	return map_create_generic(tr, ADD, SUB, process_add);
}


map map_remplace(map L, int pos, Tree* tr)
{
	int i = L->length;
	for (Cell* tmp = L->end; tmp != NULL; tmp = tmp->back)
	{
		if (i == pos + 1)
		{
			if (!strcmp(((Tree*)tmp->data)->value, "0"))
			{
				clean_tree(tmp->data);
				tmp->data = tr;
			}
			else
				tmp->data = join(tmp->data, tr, fnc[ADD].ex);
			return L;
		}
		i--;
	}
	return L;
}
