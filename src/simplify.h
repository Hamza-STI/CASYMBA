#ifndef __SIMPLIFY__H__
#define __SIMPLIFY__H__

	#include "map.h"

	extern bool ALG_EXPAND;
	extern bool LN_EXP_EXPAND;
	extern bool TRIG_EXPAND;
	extern bool RT_SIMP;
    //extern bool TRIGO_EXACT_SEARCH;

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
	bool is_negation(Tree* u);
	long long integer_gcd(long long a, long long b);
	long long int factoriel(long long int a);
	Tree* trigo_identify(const char* s, token tk);
	Tree* PGCD(Tree* A, Tree* B);
	Tree* pow_transform(Tree* u);

	/* numeric simplify */

	Tree* numerator_fun(Tree* u);
	Tree* denominator_fun(Tree* u);
	Tree* base(Tree* u);
	Tree* exponent(Tree* u);
	Tree* expand(Tree* tr);
	Tree* constant(Tree* u);
	Tree* term(Tree* u);
	Tree* factorn(long long int val);

	/* symbolic simplify */

	Tree* simplify(Tree* u);

	Tree* rationalize_expression(Tree* u);

	int ordre_tree(Tree* u, Tree* v);
	map map_sort(map li);

	Tree* Contract_pow(Tree* v);

	Tree* algebraic_expand(Tree* u);

	/* polynomial */

	bool ismonomial(Tree* u, const char* x);
	Tree* degree_sv(Tree* u, const char* x);
	Tree* degree_monomial_sv(Tree* u, const char* x);
	Tree* coefficient_gpe(Tree* u, const char* x, Tree* j);
	map poly_quotient(map u,map v);
	map poly_remainder(map u, map v);
	Tree* polyreconstitute(map Li, const char* x);
	map coefficient_monomial_gpe(Tree* u, const char* x);
	map polynomial_division(map u, map v, map* rem);
	map polycoeffs(Tree* u, const char* x);
	map poly_gcd(map u, map v);
	Tree* poly_simp(map u, map v, const char* x);

#endif
