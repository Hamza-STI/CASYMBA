#ifndef __DLIST__H__
#define __DLIST__H__

	#include <stdio.h>
	#include <stdlib.h>
	#include <string.h>

	typedef char* string;
	#define TAILLE_MAX 255

	/* Définition d'un type Booléen */
	typedef enum
	{
		false,
		true
	} bool;

	/* Définition d'un maillon de la liste */
	typedef struct DListCell
	{
		string value;
		struct DListCell* next;
		struct DListCell* back;
	} DListCell;

	/* Définition d'une liste doublement chaînée */
	typedef struct DList
	{
		int length;
		struct DListCell* begin;
		struct DListCell* end;
	} *DList;

	/*-----------------------------------*/

	DList push_back_dlist(DList li, const char* x);
	DList pop_back_dlist(DList li);
	int dlist_length(DList li);
	string dlist_last(DList li);
	DList clear_dlist(DList li);
	DList dlist_left(DList li, int length);
	DList dlist_sub(DList li, int start, int length);
	DList dlist_remove_id(DList p_list, int position);

#endif

