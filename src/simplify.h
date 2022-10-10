#ifndef __SIMPLIFY__H__
#define __SIMPLIFY__H__

	#include "map.h"

	#define iquot(a, b) ((double)(int)( a / b))

	extern bool ALG_EXPAND;
	extern bool LN_EXP_EXPAND;
	extern bool TRIG_EXPAND;
	extern bool RT_SIMP;

	int free_of(Tree* u, Tree* t);
	int ispoly(Tree* u, const char* vr);
	int is_int(Tree* u);
	bool isdemi(Tree* tr);
	bool is_negation(Tree* u);
	double integer_gcd(double a, double b);
	double factoriel(double a);
	Tree* trigo_identify(const char* s, token tk);
	Tree* PGCD(Tree* A, Tree* B);

	/* numeric simplify */

	Tree* numerator_fun(Tree* u);
	Tree* denominator_fun(Tree* u);
	Tree* base(Tree* u);
	Tree* exponent(Tree* u);
	Tree* expand(Tree* tr);
    Tree* constant(Tree* u);
    Tree* term(Tree* u);

	Tree* fracOp(const char* numerator, const char* denominator);
	Tree* sumOp(const char* left, const char* right);
	Tree* diffOp(const char* left, const char* right);
	Tree* prodOp(const char* left, const char* right);
	Tree* factOp(const char* left);
	Tree* factorn(double val);

	Tree* simplify_RNE(Tree* u);
	Tree* simplify_RNE_rec(Tree* u);
	Tree* simplify_rational_number(Tree* u);
	Tree* evaluate_power(Tree* bases, Tree* expon);
	Tree* evaluate_add(Tree* left, Tree* right);
	Tree* evaluate_diff(Tree* left, Tree* right);
	Tree* evaluate_prod(Tree* left, Tree* right);
	Tree* evaluate_quotient(Tree* left, Tree* right);

	/* symbolic simplify */ 

	Tree* simplify(Tree* u);
	Tree* simplify_power(Tree* u);
	Tree* simplify_product(map L);
	Tree* simplify_sum(map L);
	Tree* construct(const char* op, map li);
	Tree* rationalize_sum(Tree* u, Tree* v, const char* op);
	Tree* rationalize_expression(Tree* u);
	Tree* contract_exp(Tree* u);
	Tree* contract_ln_rules(Tree* u);
	Tree* contract_ln(Tree* u);
	Tree* simplify_ln(Tree* u);
	Tree* simplify_exp(Tree* u);
	Tree* expand_exp(Tree* u);
	Tree* expand_ln(Tree* u);
	Tree* trigo_simplify(Tree* u, token tk);
	Tree* absolute_value(Tree* u);

	int ordre_tree(Tree* u, Tree* v);
	map map_sort(map li);
	map simplify_product_rec(map L);
	map merge_products(map p, map q);
	map adjoin(Tree* s, map p);
	map simplify_sum_rec(map L);
	map merge_sums(map p, map q);

	Tree* absolute_value(Tree* u);
	Tree* Contract_pow(Tree* v);

	Tree* algebraic_expand(Tree* u);

	/* polynomial */

	bool ismonomial(Tree* u, const char* x);
	Tree* degree_sv(Tree* u, const char* x);
	Tree* degree_monomial_sv(Tree* u, const char* x);
	Tree* coefficient_gpe(Tree* u, const char* x, Tree* j);
	Tree* poly_gcd(Tree* u, Tree* v, const char* x);
	Tree* poly_quotient(map L);
	Tree* poly_remainder(map L);
	Tree* poly_simp(Tree* u, Tree* v, const char* x);
	map coefficient_monomial_gpe(Tree* u, const char* x);
	map polynomial_division(Tree* u, Tree* v, const char* x);

#endif
