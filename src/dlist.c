#include "dlist.h"

/* fonction g�n�rique */

List push_back(List li, void* data)
{
	Cell* element = malloc(sizeof(*element));
	element->data = data;
	element->next = NULL;
	element->back = NULL;

	if (li == NULL)
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

List push_front(List li, void* data)
{
	Cell* element = malloc(sizeof(*element));
	element->data = data;
	element->next = NULL;
	element->back = NULL;

	if (li == NULL)
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

List pop_back(List li, void (*free_data)(void*))
{
	if (li == NULL)
		return li;

	if (li->length == 1 && li->begin == li->end)
	{
		free_data(li->begin->data);
		free(li->begin);
		free(li);
		return NULL;
	}

	Cell* tmp = li->end;

	li->end = li->end->back;
	li->end->next = NULL;
	tmp->next = NULL;
	tmp->back = NULL;
	free_data(tmp->data);
	free(tmp);
	tmp = NULL;

	li->length--;
	return li;
}

List pop_front(List li, void (*free_data)(void*))
{
	if (li == NULL)
		return NULL;

	if (li->begin == li->end)
	{
		free_data(li->begin->data);
		free(li->begin);
		free(li);
		li = NULL;
		return NULL;
	}

	Cell* temp = li->begin;

	li->begin = li->begin->next;
	li->begin->back = NULL;
	temp->next = NULL;
	temp->back = NULL;

	free_data(temp->data);
	free(temp);
	temp = NULL;

	li->length--;

	return li;
}

List clear(List li, void (*free_data)(void*))
{
	if (li == NULL)
		return li;

	if (li->length == 1 && li->begin == li->end)
	{
		free_data(li->begin->data);
		free(li->begin);
		free(li);
	}
	else
	{
		Cell* tmp = li->begin;
		while (tmp != NULL)
		{
			Cell* del = tmp;
			tmp = tmp->next;
			free_data(del->data);
			free(del);
		}
		free(li);
	}

	return NULL;
}

void free_char_ptr(void* data)
{
	free(data);
}

/* ------------------------------------------------------------- */

DList push_back_dlist(DList li, const char* x)
{
	return push_back(li, strdup(x));
}

DList pop_back_dlist(DList li)
{
	return pop_back(li, free_char_ptr);
}

DList clear_dlist(DList li)
{
	return clear(li, free_char_ptr);
}

DList dlist_left(DList li, int length)
{
	return dlist_sub(li, 1, length);
}

DList dlist_sub(DList li, int start, int length)
{
	DList list = NULL;
	Cell *tmp = li->begin;
	int compte = 1;

	while(compte < start + length)
	{
		if (start <= compte && compte < start + length)
            list = push_back_dlist(list, tmp->data);
		tmp = tmp->next;
		compte++;
	}
	return list;
}

DList dlist_remove_id(DList p_list, int position)
{
	if (p_list != NULL)
	{
		Cell* p_temp = p_list->begin;
		int i = 1;
		while (p_temp != NULL && i <= position)
		{
			if (position == i)
			{
				if (p_temp->next == NULL)
				{
					p_list->end = p_temp->back;
					p_list->end->next = NULL;
				}
				else if (p_temp->back == NULL)
				{
					p_list->begin = p_temp->next;
					p_list->begin->back = NULL;
				}
				else
				{
					p_temp->next->back = p_temp->back;
					p_temp->back->next = p_temp->next;
				}
				free(p_temp->data);
				free(p_temp);
				p_list->length--;
			}
			else
			{
				p_temp = p_temp->next;
			}
			i++;
		}
	}
	return p_list;
}