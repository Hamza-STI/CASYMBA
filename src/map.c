#include "map.h"

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

map push_back_map_if(map li, Tree* arb, Tree* tr)
{
	if (li == NULL)
	{
		li = push_back_map(push_back_map(li, arb), tr);
		return li;
	}
	mapCell* tmp = li->begin;
	while (tmp != NULL)
	{
		if (tree_compare(arb, ((Tree*)tmp->data)))
			return li;
		tmp = tmp->next->next;
	}
	li = push_back_map(push_back_map(li, arb), tr);
	return li;
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
	mapCell* tmp = Li->begin;
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

map process_prod(map li, Tree* tr)
{
	Tree* r = join(new_tree("1"), NULL, fnc[NEGATIF].ex);
	Tree* s = join(clone(tr), r, fnc[POW].ex);
	li = push_front(li, s);
	return li;
}

map map_create_prod(Tree* tr)
{
	map li = NULL;
	Tree* tmp = tr;
	while (tmp->tok_type == PROD || tmp->tok_type == DIVID)
	{
		if (tmp->tright->tok_type == PROD)
		{
			map T = map_create_prod(tmp->tright);
			mapCell* tmp_T = T->begin;
			while (tmp_T != NULL)
			{
				if (tmp->tok_type == DIVID)
					li = process_prod(li, tmp_T->data);
				else
					li = push_front_map(li, tmp_T->data);
				tmp_T = tmp_T->next;
			}
			T = clear_map(T);
		}
		else if (tmp->tok_type == DIVID)
			li = process_prod(li, tmp->tright);
		else
			li = push_front_map(li, tmp->tright);
		tmp = tmp->tleft;
	}
	li = push_front_map(li, tmp);
	return li;
}

map process_add(map li, Tree* tr)
{
	if (tr->tok_type == NEGATIF)
		li = push_front_map(li, tr->tleft);
	else if (tr->tleft != NULL && tr->tleft->tok_type == NEGATIF && !strcmp(tr->tleft->tleft->value, "1"))
		li = push_front_map(li, tr->tright);
	else if (isconstant(tr) && strcmp(tr->value, "0"))
	{
		Tree* r = join(clone(tr), NULL, fnc[NEGATIF].ex);
		li = push_front(li, r);
	}
	else
	{
		Tree* r = join(new_tree("1"), NULL, fnc[NEGATIF].ex);
		Tree* s = join(r, clone(tr), fnc[PROD].ex);
		li = push_front(li, s);
	}
	return li;
}

map map_create_add(Tree* tr)
{
	map li = NULL;
	Tree* tmp = tr;
	while (tmp->tok_type == ADD || tmp->tok_type == SUB)
	{
		if (tmp->tright->tok_type == ADD || tmp->tright->tok_type == SUB)
		{
			map T = map_create_add(tmp->tright);
			mapCell* tmp_T = T->begin;
			while (tmp_T != NULL)
			{
				Tree* tr_tmp = (Tree*)tmp_T->data;
				if (tmp->tok_type == SUB)
					li = process_add(li, tr_tmp);
				else
					li = push_front_map(li, tr_tmp);
				tmp_T = tmp_T->next;
			}
			T = clear_map(T);
		}
		else if (tmp->tok_type == SUB)
			li = process_add(li, tmp->tright);
		else
			li = push_front_map(li, tmp->tright);
		tmp = tmp->tleft;
	}
	li = push_front_map(li, tmp);
	return li;
}

map map_remplace(map L, int pos, Tree* tr)
{
	int i = L->length;
	mapCell* tmp = L->end;
	while (tmp != NULL)
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
		tmp = tmp->back;
	}
	return L;
}
