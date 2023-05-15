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
	typedef struct DListCell
	{
		char *value;
		struct DListCell *next;
		struct DListCell *back;
	} DListCell;

	/* Définition d'une liste doublement chaînée */
	typedef struct DList
	{
		int length;
		struct DListCell *begin;
		struct DListCell *end;
	} *DList;

	/*-----------------------------------*/

	DList push_back_dlist(DList li, const char* x);
	DList pop_back_dlist(DList li);
	DList clear_dlist(DList li);
	DList dlist_left(DList li, int length);
	DList dlist_sub(DList li, int start, int length);
    DList dlist_remove_id(DList p_list, int position);
    DList dlist_sortD(DList li);

#endif

