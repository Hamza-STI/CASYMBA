#ifndef __MAP__H__
#define __MAP__H__

	#include "rpn.h"

	/* Définition d'un maillon de la liste */
	typedef struct mapCell
	{
		Tree* tr;
		struct mapCell *next;
		struct mapCell *back;
	} mapCell;

	/* Définition d'une liste doublement chaînée */
	typedef struct map
	{
		int length;
		struct mapCell *begin;
		struct mapCell *end;
	} *map;
	/*-----------------------------------*/

	map push_front_map(map li, Tree *tr);
	map push_back_map(map li, Tree* arb);
	map pop_back_map(map li);
	map pop_front_map(map li);
	map clear_map(map li);
	void print_map(map li);
	map map_create(Tree* tr);
	map map_create_add(Tree* tr);
	map map_create_prod(Tree* tr);
	map map_sort(map li);

#endif

