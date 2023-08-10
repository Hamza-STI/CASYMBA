#ifndef __SIMPLIFY__H__
#define __SIMPLIFY__H__

	#include "map.h"

	extern bool ALG_EXPAND;
	extern bool LN_EXP_EXPAND;
	extern bool TRIG_EXPAND;
	extern bool RT_SIMP;

	typedef struct Trigo_value
	{
		const char* angle;
		const char* cos_value;
		const char* sin_value;
		const char* tan_value;
	} Trigo_value;

	int ispoly(Tree* u, const char* vr);
	int is_int(Tree* u);
	bool isdemi(Tree* tr);
	long long int factoriel(int a);
	Tree* trigo_identify(const char* s, token tk);
	Tree* PGCD(Tree* A, Tree* B);
	Tree* pow_transform(Tree* u);

	/* numeric simplify */

	Tree* numerator_fun(Tree* u);
	Tree* denominator_fun(Tree* u);
	Tree* base(Tree* u);
	Tree* exponent(Tree* u);
	Tree* expand(Tree* tr);
	Tree* factorn(int val);

	/* symbolic simplify */

	Tree* simplify(Tree* u);

	Tree* rationalize_expression(Tree* u);

	bool ordre_tree(Tree* u, Tree* v);
	map map_sort(map li);

	Tree* Contract_pow(Tree* v);

	Tree* algebraic_expand(Tree* u);

	/* polynomial */

	bool ismonomial(Tree* u, const char* x);
	Tree* degree_sv(Tree* u, const char* x);
	Tree* coefficient_gpe(Tree* u, const char* x, unsigned j);
	map poly_quotient(map u,map v, token tk);
	Tree* polyreconstitute(map* Li, const char* x);
	map polynomial_division(map* u, map* v, map* rem);
	map polycoeffs(Tree* u, const char* x);
	map poly_gcd(map u, map v);
	Tree* poly_simp(map u, map v, const char* x);

	typedef Tree* (*TreeOperation)(const char*, const char*);

#endif
