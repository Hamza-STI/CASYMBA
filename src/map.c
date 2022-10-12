#include "map.h"

map push_front_map(map li, Tree *tr)
{
	mapCell *element = malloc(sizeof(*element));
	element->tr = clone(tr);
	element->next = NULL;
	element->back = NULL;

	if(li == NULL)
	{
		li = malloc(sizeof(*li));

		li->length = 0;
		li->begin = element;
		li->end = element;
	}
	else
	{
		li->begin->back = element;
		element->next = li->begin;
		li->begin = element;
	}

	li->length++;

	return li;
}

map push_back_map(map li, Tree* arb)
{
	mapCell *element = malloc(sizeof(*element));
	element->tr = clone(arb);
	element->next = NULL;
	element->back = NULL;

	if(li == NULL)
	{
		li = malloc(sizeof(*li));

		li->length = 0;
		li->begin = element;
		li->end = element;
	}
	else
	{
		li->end->next = element;
		element->back = li->end;
		li->end = element;
	}

	li->length++;
	return li;
}

map pop_back_map(map li)
{
	if(li == NULL)
		return NULL;

	if(li->begin == li->end)
	{
		clean_tree(li->end->tr);
		free(li->end);
		free(li);
		li = NULL;

		return NULL;
	}

	mapCell *temp = li->end;

	li->end = li->end->back;
	li->end->next = NULL;
	temp->next = NULL;
	temp->back = NULL;

	clean_tree(temp->tr);
	free(temp);
	temp = NULL;

	li->length--;

	return li;
}

map pop_front_map(map li)
{
	if(li == NULL)
	{
		return NULL;
	}

	if(li->begin == li->end)
	{
		clean_tree(li->begin->tr);
		free(li->begin);
		free(li);
		li = NULL;
		return NULL;
	}

	mapCell *temp = li->begin;

	li->begin = li->begin->next;
	li->begin->back = NULL;
	temp->next = NULL;
	temp->back = NULL;

	clean_tree(temp->tr);
	free(temp);
	temp = NULL;

	li->length--;

	return li;
}

map clear_map(map li)
{
	if(li == NULL)
		return li;

	if(li->length == 1 && li->begin == li->end)
	{
		clean_tree(li->begin->tr);
		free(li->begin);
		free(li);
	}
	else
	{
		mapCell *tmp = li->begin;

		while(tmp != NULL)
		{
			mapCell *del = tmp;
			tmp = tmp->next;
			clean_tree(del->tr);
			free(del);
		}
		free(li);
	}

	return NULL;
}

void print_map(map li)
{
	if(li == NULL)
	{
		printf("Rien a afficher, la map est vide.\n");
		return;
	}

	mapCell *temp = li->begin;

	while(temp != NULL)
	{
		printf("nouvel arbre\n");
		print_tree_prefix(temp->tr);
		temp = temp->next;
	}

	printf("\n");
}

map map_create(Tree *tr)
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

map map_create_prod(Tree* tr)
{
	map li = NULL;
	Tree *tmp = tr;
	while (tmp->tok_type == PROD || tmp->tok_type == DIVID)
	{
		if (tmp->tright->tok_type == PROD)
		{
			map T = map_create_prod(tmp->tright);
			mapCell* tmp_T = T->begin;
			while (tmp_T != NULL)
			{
				if (tmp->tok_type == DIVID)
				{
					Tree* r = join(new_tree("1"), NULL, "~");
					Tree* s = join(clone(tmp_T->tr), r, "^");
					li = push_front_map(li, s);
					clean_tree(s);
				}
				else
					li = push_front_map(li, tmp_T->tr);
				tmp_T = tmp_T->next;
			}
			T = clear_map(T);
		}
		else if (tmp->tok_type == DIVID)
		{	
			Tree *r =  join(new_tree("1"), NULL, "~" );
			Tree *s = join( clone(tmp->tright), r, "^" );
			li = push_front_map(li, s);
			clean_tree(s);
		}
		else
			li = push_front_map(li, tmp->tright);
		tmp = tmp->tleft;
	}
	li = push_front_map(li, tmp);
	return map_sort(li);
}

map map_create_add(Tree* tr)
{
	map li = NULL;
	Tree *tmp = tr;
	while (tmp->tok_type == ADD || tmp->tok_type == SUB)
	{
		if (tmp->tright->tok_type == ADD || tmp->tright->tok_type == SUB)
		{
			map T = map_create_add(tmp->tright);
			mapCell* tmp_T = T->begin;
			while (tmp_T != NULL)
			{
				if (tmp->tok_type == SUB)
				{
					if (tmp_T->tr->tok_type == NEGATIF)
						li = push_front_map(li, tmp_T->tr->tleft);
					else if (tmp_T->tr->tleft->tok_type == NEGATIF)
						li = push_front_map(li, tmp_T->tr->tright);
					else if (isconstant(tmp_T->tr))
					{
						if (strcmp(tmp_T->tr->value, "0"))
						{
							Tree* r = join(clone(tmp->tright), NULL, "~");
							li = push_front_map(li, r);
							clean_tree(r);
						}
					}
					else
					{
						Tree* r = join(new_tree("1"), NULL, "~");
						Tree* s = join(r, clone(tmp_T->tr), "*");
						li = push_front_map(li, s);
						clean_tree(s);
					}
				}
				else
					li = push_front_map(li, tmp_T->tr);
				tmp_T = tmp_T->next;
			}
			T = clear_map(T);
		}
		else if (tmp->tok_type == SUB)
		{	
			if (isconstant(tmp->tright))
			{
				if (strcmp(tmp->tright->value, "0"))
				{
					Tree* r = join(clone(tmp->tright), NULL, "~");
					li = push_front_map(li, r);
					clean_tree(r);
				}
			}
			else
			{
				Tree* r = join(new_tree("1"), NULL, "~");
				Tree* s = join(r, clone(tmp->tright), "*");
				li = push_front_map(li, s);
				clean_tree(s);
			}
		}
		else
			li = push_front_map(li, tmp->tright);
		tmp = tmp->tleft;
	}
	li = push_front_map(li, tmp);
	return map_sort(li);
}

map map_remplace(map L, int pos, Tree* tr)
{
	int i = L->length;
	mapCell* tmp = L->end;
	while (tmp != NULL)
	{
		if (i == pos + 1)
		{
			if (!strcmp(tmp->tr->value, "0"))
			{
				clean_tree(tmp->tr);
				tmp->tr = tr;
				return L;
			}
			else
			{
				tmp->tr = join(tmp->tr, tr, fnc[ADD].ex);
				return L;
			}
		}
		i--;
		tmp = tmp->back;
	}
	return L;
}
