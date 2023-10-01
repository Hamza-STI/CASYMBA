#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef _EZ80

#include <tice.h>
#include <fileioc.h>

#endif // _EZ80

#ifndef __DLIST__H__
#define __DLIST__H__

	typedef char* string;
	#define TAILLE_MAX 256

	/* Définition d'un maillon de la liste */
	typedef struct Cell
	{
		void* data;
		struct Cell* next;
		struct Cell* back;
	} Cell;

	/* Définition d'une liste doublement chaînée */
	typedef struct List
	{
		int length;
		struct Cell* begin;
		struct Cell* end;
	} *List;

	typedef List DList;

	/* fonctions génériques */

	List push_back(List li, void* data);
	List push_front(List li, void* data);
	List pop_back(List li, void (*free_data)(void*));
	List pop_front(List li, void (*free_data)(void*));
	List clear(List li, void (*free_data)(void*));

	/*-----------------------------------*/

	DList push_back_dlist(DList li, const char* x);
	DList pop_back_dlist(DList li);
	DList clear_dlist(DList li);
	DList dlist_left(DList li, int length);
	DList dlist_sub(DList li, int start, int length);
    DList dlist_remove_id(DList p_list, int position);

#endif

