#ifndef __MAP__H__
#define __MAP__H__

	#include "rpn.h"

	/* Définition d'un maillon de la liste */

	typedef List map;
	typedef Cell mapCell;

	/*-----------------------------------*/

	map push_front_map(map li, Tree* tr);
	map push_back_map(map li, Tree* arb);
	map pop_back_map(map li);
	map pop_front_map(map li);
	map clear_map(map li);
	map clone_map(map Li);
	map map_create(Tree* tr);
	map map_create_add(Tree* tr);
	map map_create_prod(Tree* tr);
	map map_sort(map li);
	map map_remplace(map L, int pos, Tree* tr);
	map push_back_map_if(map li, Tree* arb, Tree* tr);

    typedef map (ProcessFunction)(map, Tree*);

#endif

