#include "dlist.h"


DList push_back_dlist(DList li, const char* x)
{
	DListCell *element = malloc(sizeof(*element));
	element->value = malloc(strlen(x) + 1);
	memcpy(element->value, x, strlen(x) + 1);
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

DList pop_back_dlist(DList li)
{
	if(li == NULL)
		return li;

	if(li->length == 1 && li->begin == li->end)
	{
		free(li->begin->value);
		free(li->begin);	
		free(li);
		return NULL;
	}

	DListCell *tmp = li->end;

	li->end = li->end->back;
	li->end->next = NULL;
	tmp->next = NULL;
	tmp->back = NULL;
	free(tmp->value);
	free(tmp);
	tmp = NULL;

	li->length--;
	return li;
}

int dlist_length(DList li)
{
	if(li == NULL)
		return 0;

	return li->length;
}

string dlist_last(DList li)
{
	if(li == NULL)
	{
		static char r[2] = "\0";
		return r;
	}
	
	return li->end->value;
}

DList clear_dlist(DList li)
{
	if(li == NULL)
		return li;

	if(li->length == 1 && li->begin == li->end)
	{
		free(li->begin->value);
		free(li->begin);
		free(li);
	}
	else
	{
		DListCell *tmp = li->begin;

		while(tmp != NULL)
		{
			DListCell *del = tmp;
			tmp = tmp->next;
			free(del->value);
			free(del);
		}
		free(li);
	}

	return NULL;
}

DList dlist_left(DList li, int length)
{
	DList gauche = NULL;
	DListCell *tmp = li->begin;
	int compte = 1;

	while(compte <= length)
	{
		string new_value  = tmp->value;
		gauche = push_back_dlist(gauche, new_value);
		tmp = tmp->next;
		compte++;
	}
	return gauche;
}

DList dlist_sub(DList li, int start, int length)
{
	DList list = NULL;
	DListCell *tmp = li->begin;
	int compte = 1;

	while(compte < start + length)
	{
		if (start <= compte && compte < start + length)
		{
			list = push_back_dlist(list, tmp->value);
		}
		tmp = tmp->next;
		compte++;
	}
	return list;
}

DList dlist_remove_id(DList p_list, int position)
{
	if (p_list != NULL)
	{
		DListCell* p_temp = p_list->begin;
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
				free(p_temp->value);
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