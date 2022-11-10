#ifndef __SIMPLIFY__H__
#define __SIMPLIFY__H__

	#include "map.h"

	#define iquot(a, b) ((double)(int)( a / b))

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
	int integer_gcd(int a, int b);
	double factoriel(double a);
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
	Tree* poly_quotient(map L);
	Tree* poly_remainder(map L);
	map coefficient_monomial_gpe(Tree* u, const char* x);
	map polynomial_division(Tree* u, Tree* v, const char* x);
	Tree* poly_gcd(Tree* u, Tree* v, const char* x);
	Tree* poly_simp(Tree* u, Tree* v, const char* x);

#endif
