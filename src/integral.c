#include "integral.h"

#define AMOUNT_INTEGRAL 164
#define AMOUNT_DERIV 18
int ipp_loop = 10;
char int_cond[10] = { 0 };

static Tree* integral_form(Tree* u, const char* x, map* L);

static map separate_factor(Tree* u, const char* x)
{
	if (!found_element(u, x))
		return push_back_map_s(push_back_map(NULL, u), new_tree("1"));
	if (u->tok_type == DIVID || u->tok_type == PROD)
	{
		map f = separate_factor(u->tleft, x), g = separate_factor(u->tright, x);
		Tree* free_of_part = join(clone(f->begin->tr), clone(g->begin->tr), fnc[u->tok_type].ex);
		Tree* dependent_part = join(clone(f->end->tr), clone(g->end->tr), fnc[u->tok_type].ex);
		f = clear_map(f); g = clear_map(g);
		return push_back_map_s(push_back_map_s(NULL, free_of_part), dependent_part);
	}
	return push_back_map(push_back_map_s(NULL, new_tree("1")), u);
}

static int priority_int(Tree* a, const char* x)
{
	/*Ln - Inv trig (1 - 2) - Alg - Trig  (1 - 2) - Exp*/
	token A = a->tok_type;
	if (A == LN_F)
		return 7;
	if (ACOS_F <= A && A <= ATAN_F)
		return 6;
	if (ACOSH_F <= A && A <= ATANH_F)
		return 5;
	if (A == SQRT_F || A == POW)
		return priority_int(a->tleft, x);
	if (ispoly(a, x))
		return 4;
	if (COS_F <= A && A <= TAN_F)
		return 3;
	if (COSH_F <= A && A <= TANH_F)
		return 2;
	if (A == EXP_F)
		return 1;
	if (a->gtype == OPERAT)
	{
		int u = priority_int(a->tleft, x), v = priority_int(a->tright, x);
		return (u > v) ? u : v;
	}
	return 0;
}

map polycoeffs(Tree* u, const char* x)
{
	int i = 1;
	map cf = NULL;
	Tree* z = new_tree("0");
	Tree* r = simplify(remplace_tree(u, x, z)), * d = diff(u, x);
	cf = push_back_map_s(cf, r);
	while (strcmp(d->value, "0"))
	{
		r = simplify(remplace_tree(d, x, z));
		r = simplify(join(r, new_tree(tostr(factoriel(i))), fnc[DIVID].ex));
		cf = push_front_map(cf, r);
		clean_tree(r);
		Tree* tmp = diff(d, x);
		clean_tree(d);
		d = tmp;
		i++;
	}
	clean_tree(d);
	clean_tree(z);
	return cf;
}

/* calcul derivee */

static Tree* form_integral(const char* s_form, struct Integral* w, int size)
{
	for (const Integral* element = w; element != w + size; element++)
	{
		unsigned i = strlen(element->condt);
		if (!strcmp(element->expr, s_form) && (i == 0 || (i && (strstr(element->condt, int_cond) != NULL || strstr(int_cond, element->condt) != NULL))))
			return to_tree(In2post2(element->calc));
	}
	return NULL;
}

struct Integral Derivtable[] =
{
	{ fnc[LN_F].ex, "V/U", "" },
	{ fnc[LOG_F].ex, "V/(U*ln(10))", "" },
	{ fnc[EXP_F].ex, "V*exp(U)", "" },
	{ fnc[ABS_F].ex, "V*sign(U)", "" },
	{ fnc[SQRT_F].ex, "V/(2*sqrt(U))", "" },
	{ fnc[COS_F].ex, "~V*sin(U)", "" },
	{ fnc[SIN_F].ex, "V*cos(U)", "" },
	{ fnc[TAN_F].ex, "V/cos(U)^2", "" },
	{ fnc[COSH_F].ex, "V*sinh(U)", "" },
	{ fnc[SINH_F].ex, "V*cosh(U)", "" },
	{ fnc[TANH_F].ex, "V/cosh(U)^2", "" },
	{ fnc[ACOS_F].ex, "~V/sqrt(1-U^2)", "" },
	{ fnc[ASIN_F].ex, "V/sqrt(1-U^2)", "" },
	{ fnc[ATAN_F].ex, "V/(U^2+1)", "" },
	{ fnc[ACOSH_F].ex, "V/sqrt(U^2-1)", "" },
	{ fnc[ASINH_F].ex, "V/sqrt(1+U^2)", "" },
	{ fnc[ATANH_F].ex, "V/(1-U^2)", "" },
	{ fnc[CBRT_F].ex, "V/(3*U^(2/3))", "" }
};

Tree* diff(Tree* tr, const char* vr)
{
	if (!found_element(tr, vr))
		return new_tree("0");
	if (!strcmp(tr->value, vr))
		return new_tree("1");
	optype op = tr->gtype;
	string sig = tr->value;
	token tok = tr->tok_type;
	if (op == OPERAT)
	{
		Tree* dl = diff(tr->tleft, vr), * dr = diff(tr->tright, vr);
		if (tok == ADD || tok == SUB)
			return simplify(join(dl, dr, sig));
		if (tok == PROD || tok == DIVID)
		{
			Tree* t = simplify(join(join(dl, clone(tr->tright), fnc[PROD].ex), join(dr, clone(tr->tleft), fnc[PROD].ex), fnc[(tok == PROD) ? ADD : SUB].ex));
			return (tok == PROD) ? t : join(t, join(clone(tr->tright), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
		}
		if (tok == POW)
		{
			Tree* sol = NULL;
			bool v = !strcmp(dr->value, "0");
			if (v || !strcmp(dl->value, "0"))
			{
				sol = to_tree(In2post2(v ? "C*V*U^(C-1)" : "V*ln(C)*C^U"));
				sol = remplace_var(remplace_var(remplace_var(sol, "U", v ? tr->tleft : tr->tright), "V", v ? dl : dr), "C", v ? tr->tright : tr->tleft);
			}
			else
				sol = remplace_var(remplace_var(remplace_var(remplace_var(to_tree(In2post2("(T*V/U+ln(U)*W)*U^V")), "U", tr->tleft), "V", tr->tright), "T", dl), "W", dr);
			clean_tree(dr); clean_tree(dl);
			return sol;
		}
	}
	else if (tok == NEGATIF)
		return join(simplify(diff(tr->tleft, vr)), NULL, sig);
	if (tok == INTEGRAL_F)
	{
		Tree* t = tr;
		while (t->tleft->tok_type == SEPARATEUR)
			t = t->tleft;
		return clone(t->tleft);
	}
	if (tok == LOGBASE_F || tok == ROOT_F)
	{
		Tree* dl = simplify(diff(tr->tleft->tleft, vr)), * sol = to_tree(In2post2((tok == LOGBASE_F) ? "V/(U*ln(C))" : "V/(C*U^((C-1)/C))"));
		sol = remplace_var(remplace_var(remplace_var(sol, "U", tr->tleft->tleft), "V", dl), "C", tr->tleft->tright);
		clean_tree(dl);
		return sol;
	}
	Tree* dl = simplify(diff(tr->tleft, vr));
	Tree* sol = form_integral(sig, Derivtable, AMOUNT_DERIV);
	if (sol != NULL)
	{
		sol = remplace_var(remplace_var(sol, "U", tr->tleft), "V", dl);
		clean_tree(dl);
		return sol;
	}
	clean_tree(dl);
	return join(join(join(clone(tr), new_tree(vr), fnc[SEPARATEUR].ex), new_tree(vr), fnc[SEPARATEUR].ex), NULL, fnc[DERIV_F].ex);
}

/* primitive */

static Tree* function_form(int var, Tree* u, const char* x, map* L)
{
	map cf1 = polycoeffs(u->tleft, x);
	if (cf1->length == 2)
	{
		Tree* a = new_tree((var == 1) ? "A" : "B");
		if (!ismonomial(u->tleft, x))
		{
			Tree* b = join(clone(a), new_tree("X"), fnc[PROD].ex);
			*L = push_back_map_if(*L, b, u->tleft);
		}
		Tree* tr = cf1->begin->tr;
		token tk = u->tok_type;
		if (((ACOS_F <= tk && tk <= ATAN_F) || (ACOSH_F <= tk && tk <= ATANH_F)) && tr->tok_type == DIVID && !strcmp(tr->tleft->value, "1"))
		{
			*L = push_back_map_if(*L, a, tr->tright);
			cf1 = clear_map(cf1);
			return join(join(new_tree("X"), a, fnc[DIVID].ex), NULL, u->value);
		}
		*L = push_back_map_if(*L, a, tr);
		cf1 = clear_map(cf1);
		return join(join(a, new_tree("X"), fnc[PROD].ex), NULL, u->value);
	}
	cf1 = clear_map(cf1);
	return NULL;
}

static Tree* integral_sub2(Tree* u)
{
	if (u->tok_type == INTEGRAL_F)
	{
		u->tleft->tleft = pow_transform(simplify(u->tleft->tleft));
		return integral(u->tleft->tleft, u->tleft->tright->value);
	}
	if (u->tok_type == NEGATIF)
		return join(integral_sub2(u->tleft), NULL, u->value);
	if (u->gtype == OPERAT)
		return join(integral_sub2(u->tleft), integral_sub2(u->tright), u->value);
	return clone(u);
}

static Tree* integral_sub(Tree* u, map* v)
{
	if ((*v) != NULL)
	{
		mapCell* tmp = (*v)->begin;
		while (tmp != NULL)
		{
			Tree* tr = substitute(u, tmp->tr, tmp->next->tr);
			clean_tree(u);
			u = tr;
			tmp = tmp->next->next;
		}
		*v = clear_map(*v);
	}
	Tree* w = integral_sub2(u);
	clean_tree(u);
	return w;
}

static map trial_substitutions(Tree* f, map L)
{
	if (f->tok_type == POW || f->gtype == FUNCTION)
	{
		L = push_back_map(L, f);
		return L;
	}
	else if (f->gtype == OPERAT)
	{
		L = trial_substitutions(f->tleft, L);
		L = trial_substitutions(f->tright, L);
	}
	else if (f->tok_type == NEGATIF)
		L = trial_substitutions(f->tleft, L);
	return L;
}

static Tree* add_form(Tree* u, const char* x, map* L)
{
	if (ispoly(u, x))
	{
		map coefs = polycoeffs(u, x);
		if (coefs->length == 2)
		{
			int k = (*L == NULL) ? 0 : (*L)->length;
			Tree* a = new_tree("A"), * b = new_tree("B");
			*L = push_back_map_if(*L, a, coefs->begin->tr);
			if (k == (*L)->length)
			{
				clean_tree(a); clean_tree(b);
				a = new_tree("P"); b = new_tree("Q");
			}
			*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->end->tr);
			coefs = clear_map(coefs);
			return join(join(a, new_tree("X"), fnc[PROD].ex), b, fnc[ADD].ex);
		}

		if (ismonomial(u->tleft, x) && ismonomial(u->tright, x))
		{
			if (strcmp(coefs->begin->next->tr->value, "0"))
			{
				int k = coefs->length - 2;
				Tree* a = new_tree("A"), * b = new_tree("B");
				*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->begin->next->tr);
				coefs = clear_map(coefs);
				if (k == 1)
					return join(new_tree("X"), join(join(a, new_tree("X"), fnc[PROD].ex), b, fnc[ADD].ex), fnc[PROD].ex);
				Tree* m = new_tree("M"), * m_value = new_tree(tostr(k));
				*L = push_back_map_if(*L, m, m_value);
				clean_tree(m_value);
				Tree* q = join(new_tree("X"), m, fnc[POW].ex);
				return join(q, join(join(a, new_tree("X"), fnc[PROD].ex), b, fnc[ADD].ex), fnc[PROD].ex);
			}
			if (strcmp(coefs->begin->tr->value, "0") && strcmp(coefs->end->tr->value, "0"))
			{
				int k = coefs->length;
				Tree* a = new_tree("A"), * c = new_tree("C"), * n = new_tree((k == 3) ? "2" : "N");
				if (k > 3)
				{
					Tree* val = new_tree(tostr(k - 1));
					*L = push_back_map_if(*L, n, val);
					clean_tree(val);
				}
				*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), c, coefs->end->tr);
				sprintf(int_cond, "a%s0 c%s0", (coefs->begin->tr->tok_type == NEGATIF) ? "<" : ">", (coefs->end->tr->tok_type == NEGATIF) ? "<" : ">");
				coefs = clear_map(coefs);
				return join(c, join(a, join(new_tree("X"), n, fnc[POW].ex), fnc[PROD].ex), fnc[ADD].ex);
			}
		}
		if (coefs->length == 3)
		{
			Tree* fct = square_free_factor(u, x);
			if (fct->tok_type == PROD || fct->tok_type == POW)
			{
				if (fct->tok_type == POW)
				{
					coefs = clear_map(coefs);
					coefs = polycoeffs(fct->tleft, x);
					Tree* a = new_tree("A"), * b = new_tree("B"), * n = new_tree("N");
					*L = push_back_map_if(push_back_map_if(push_back_map_if(*L, n, fct->tright), a, coefs->begin->tr), b, coefs->end->tr);
					coefs = clear_map(coefs);
					return join(join(join(a, new_tree("X"), fnc[PROD].ex), b, fnc[ADD].ex), n, fnc[POW].ex);
				}
				if (fct->tok_type == PROD && (fct->tleft->tok_type == ADD || fct->tleft->tok_type == SUB) && (fct->tright->tok_type == ADD || fct->tright->tok_type == SUB))
				{
					coefs = clear_map(coefs);
					map cfs = polycoeffs(fct->tright, x);
					coefs = polycoeffs(fct->tleft, x);
					Tree* a = new_tree("A"), * b = new_tree("B"), * p = new_tree("P"), * q = new_tree("Q");
					*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->end->tr);
					*L = push_back_map_if(push_back_map_if(*L, p, cfs->begin->tr), q, cfs->end->tr);
					coefs = clear_map(coefs); cfs = clear_map(cfs);
					return join(join(join(a, new_tree("X"), fnc[PROD].ex), b, fnc[ADD].ex), join(join(p, new_tree("X"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[PROD].ex);
				}
			}
			clean_tree(fct);
			Tree* t = join(clone(coefs->end->back->tr), new_tree("2"), fnc[POW].ex);
			Tree* r = join(join(new_tree("4"), clone(coefs->begin->tr), fnc[PROD].ex), clone(coefs->end->tr), fnc[PROD].ex);
			t = simplify(join(t, r, fnc[SUB].ex));
			if (isconstant(t))
			{
				double n = Eval(t);
				if (n > 0)
					strcpy(int_cond, "B^2>4AC");
				else if (n == 0)
					strcpy(int_cond, "B^2=4AC");
				else
					strcpy(int_cond, "B^2<4AC");
			}
			clean_tree(t);
			Tree* a = new_tree("A"), * b = new_tree("B"), * c = new_tree("C");
			*L = push_back_map_if(push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->end->back->tr), c, coefs->end->tr);
			coefs = clear_map(coefs);
			a = join(a, join(new_tree("X"), new_tree("2"), fnc[POW].ex), fnc[PROD].ex);
			b = join(b, new_tree("X"), fnc[PROD].ex);
			return join(join(a, b, fnc[ADD].ex), c, fnc[ADD].ex);
		}
		coefs = clear_map(coefs);
	}
	Tree* f = integral_form(u->tleft, x, L), * g = integral_form(u->tright, x, L);
	if (f == NULL || g == NULL)
	{
		clean_tree(f);
		clean_tree(g);
		return NULL;
	}
	return join(f, g, u->value);
}

static Tree* prod_form(Tree* u, Tree* v, const char* x, map* L, token op)
{
	if (u->tok_type == POW && v->tok_type == POW)
	{
		token tk = u->tleft->tok_type, tk0 = v->tleft->tok_type;
		if (tree_compare(u->tright, v->tright) && trig_tok(tk) && trig_tok(tk0) && ispoly(u->tleft->tleft, x) && ispoly(v->tleft->tleft, x))
		{
			Tree* g = function_form(1, u->tleft, x, L), * h = function_form(tree_compare(u->tleft->tleft, v->tleft->tleft), v->tleft, x, L);
			if (g == NULL || h == NULL)
			{
				clean_tree(g);
				clean_tree(h);
				return NULL;
			}
			Tree* n = (!strcmp(u->tright->value, "2") && ((tk == SINH_F && tk0 == COSH_F) || (tk0 == SINH_F && tk == COSH_F))) ? clone(u->tright) : new_tree("N");
			if (!strcmp(n->value, "N"))
				*L = push_back_map_if(*L, n, u->tright);
			return join(join(g, n, fnc[POW].ex), join(h, n, fnc[POW].ex), fnc[op].ex);
		}
		if (op == PROD && !strcmp(v->tleft->value, x))
			return prod_form(v, u, x, L, op);
		if (op == DIVID && ((tk == COS_F && tk0 == SIN_F) || (tk == COSH_F && tk0 == SINH_F) || (tk0 == COS_F && tk == SIN_F) || (tk0 == COSH_F && tk == SINH_F)) && ispoly(u->tleft->tleft, x) && tree_compare(u->tleft->tleft, v->tleft->tleft))
		{
			Tree* g = function_form(1, u->tleft, x, L), * h = function_form(1, v->tleft, x, L);
			if (g == NULL || h == NULL)
			{
				clean_tree(g);
				clean_tree(h);
				return NULL;
			}
			Tree* f = simplify(join(clone(v->tright), clone(u->tright), fnc[SUB].ex));
			if (!strcmp(f->value, "2"))
			{
				clean_tree(f);
				Tree* n = new_tree("N");
				*L = push_back_map_if(*L, n, u->tright);
				return join(join(g, n, fnc[POW].ex), join(h, join(n, new_tree("2"), fnc[ADD].ex), fnc[POW].ex), fnc[op].ex);
			}
			clean_tree(f);
		}
		Tree* m = new_tree("M"), * n = new_tree("N");
		*L = push_back_map_if(*L, m, u->tright);
		int b = (*L == NULL) ? 0 : (*L)->length;
		*L = push_back_map_if(*L, n, v->tright);
		if (b == (*L)->length)
		{
			clean_tree(n);
			n = new_tree("r");
			*L = push_back_map_if(*L, n, v->tright);
		}
		Tree* f = integral_form(u->tleft, x, L), * g = integral_form(v->tleft, x, L);
		if (op == DIVID && ismonomial(u->tleft, x) && !strcmp(u->tleft->value, x))
		{
			Tree* s = simplify(join(join(new_tree("2"), clone(v->tright), fnc[PROD].ex), new_tree("1"), fnc[SUB].ex));
			if (tree_compare(s, u->tright))
				sprintf(int_cond, "m=2n-1");
			clean_tree(s);
		}
		if (f == NULL || g == NULL)
		{
			clean_tree(f);
			clean_tree(g);
			clean_tree(m);clean_tree(n);
			return NULL;
		}
		return join(join(f, m, fnc[POW].ex), join(g, n, fnc[POW].ex), fnc[op].ex);
	}
	if (u->tok_type == POW && trig_tok(u->tleft->tok_type) && trig_tok(v->tok_type) && tree_compare(u->tleft->tleft, v->tleft) && ispoly(v->tleft, x))
	{
		Tree* g = function_form(1, u->tleft, x, L), * h = function_form(1, v, x, L);
		if (g == NULL || h == NULL)
		{
			clean_tree(g);
			clean_tree(h);
			return NULL;
		}
		Tree* n = new_tree("N");
		*L = push_back_map_if(*L, n, u->tright);
		return join(join(g, n, fnc[POW].ex), h, fnc[op].ex);
	}
	if (v->tok_type == POW && trig_tok(v->tleft->tok_type) && trig_tok(u->tok_type) && tree_compare(v->tleft->tleft, u->tleft) && ispoly(u->tleft, x))
	{
		Tree* g = function_form(1, u, x, L), * h = function_form(1, v->tleft, x, L);
		if (g == NULL || h == NULL)
		{
			clean_tree(g);
			clean_tree(h);
			return NULL;
		}
		Tree* n = new_tree("N");
		*L = push_back_map_if(*L, n, u->tright);
		return join( g, join(h, n, fnc[POW].ex), fnc[op].ex);
	}
	if ((trig_tok(u->tok_type) || u->tok_type == EXP_F) && (trig_tok(v->tok_type) || v->tok_type == EXP_F) && ispoly(u->tleft, x) && ispoly(v->tleft, x))
	{
		Tree* g = function_form(1, u, x, L), * h = function_form(tree_compare(v->tleft, u->tleft), v, x, L);
		if (g == NULL || h == NULL)
		{
			clean_tree(g);
			clean_tree(h);
			return NULL;
		}
		return join(g, h, fnc[op].ex);
	}
	if (v->tok_type == SQRT_F && ispoly(u, x))
	{
		Tree* dg = degree_sv(u, x);
		Tree* f = integral_form(v, x, L);
		if (f == NULL)
		{
			clean_tree(dg);
			return NULL;
		}
		if (!strcmp(dg->value, "0") || !strcmp(dg->value, fnc[UNDEF].ex))
		{
			clean_tree(dg);
			if (op == PROD)
				return f;
			return join(new_tree("1"), f, fnc[op].ex);
		}
		if (!strcmp(dg->value, "1"))
		{
			if (!ismonomial(u, x))
			{
				map cf = polycoeffs(u, x);
				Tree* p = new_tree("P"), * q = new_tree("Q");
				*L = push_back_map_if(push_back_map_if(*L, p, cf->begin->tr), q, cf->end->tr);
				cf = clear_map(cf); clean_tree(dg);
				dg = join(join(p, new_tree("X"), fnc[PROD].ex), q, fnc[ADD].ex);
				return join(dg, f, fnc[op].ex);
			}
			clean_tree(dg);
			return join(new_tree("X"), f, fnc[op].ex);
		}
		if (ismonomial(u, x))
		{
			Tree* m = new_tree("M");
			*L = push_back_map_if(*L, m, dg);
			clean_tree(dg);
			return join(join(new_tree("X"), m, fnc[POW].ex), f, fnc[op].ex);
		}
		clean_tree(dg);
	}
	if (u->tok_type == SQRT_F && ispoly(v, x))
	{
		if (op == PROD)
			return prod_form(v, u, x, L, op);
		Tree* dg = degree_sv(v, x);
		Tree* f = integral_form(u, x, L);
		if (f == NULL)
		{
			clean_tree(dg);
			return NULL;
		}
		if (!strcmp(dg->value, "1"))
		{
			clean_tree(dg);
			if (!ismonomial(v, x))
			{
				map cf = polycoeffs(v, x);
				Tree* p = new_tree("P"), * q = new_tree("Q");
				*L = push_back_map_if(push_back_map_if(*L, p, cf->begin->tr), q, cf->end->tr);
				cf = clear_map(cf);
				return join(f, join(join(p, new_tree("X"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[op].ex);
			}
			return join(f, new_tree("X"), fnc[op].ex);
		}
		if (ismonomial(v, x))
		{
			Tree* m = new_tree("M");
			*L = push_back_map_if(*L, m, dg);
			clean_tree(dg);
			if (op == PROD)
				return join(join(new_tree("X"), m, fnc[POW].ex), f, fnc[op].ex);
			return join(f, join(new_tree("X"), m, fnc[POW].ex), fnc[op].ex);
		}
		clean_tree(dg);
	}
	if (ispoly(u, x) && ispoly(v, x))
	{
		map cf = polycoeffs(u, x), cf1 = polycoeffs(v, x);
		if (cf->length == 2 && cf1->length == 2)
		{
			Tree* a = new_tree("A"), * b = new_tree("B"), * p = new_tree("P"), * q = new_tree("Q");
			*L = push_back_map_if(push_back_map_if(*L, p, cf1->begin->tr), q, cf1->end->tr);
			*L = push_back_map_if(push_back_map_if(*L, a, cf->begin->tr), b, cf->end->tr);
			cf = clear_map(cf); cf1 = clear_map(cf1);
			return join(join(join(a, new_tree("X"), fnc[PROD].ex), b, fnc[ADD].ex), join(join(p, new_tree("X"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[op].ex);
		}
		cf = clear_map(cf); cf1 = clear_map(cf1);
	}
	if (ismonomial(v, x) && !ismonomial(u, x) && op == PROD)
		return prod_form(v, u, x, L, op);
	Tree* f = integral_form(u, x, L), * g = integral_form(v, x, L);
	if (f == NULL || g == NULL)
	{
		clean_tree(f);
		clean_tree(g);
		return NULL;
	}
	if (op == DIVID && !found_element(u, x))
	{
		clean_tree(f);
		f = new_tree("1");
	}
	return join(f, g, fnc[op].ex);
}

Tree* integral_form(Tree* u, const char* x, map* L)
{
	if (!found_element(u, x))
	{
		Tree* v = simplify(clone(u));
		if (!strcmp(v->value, "1"))
			return v;
		Tree* c = new_tree("C");
		*L = push_back_map_if(*L, c, v);
		clean_tree(v);
		return c;
	}
	if (!strcmp(u->value, x))
		return new_tree("X");
	token utok = u->tok_type;
	if ((utok == COS_F || utok == SIN_F) && u->tleft->tok_type == LN_F && ispoly(u->tleft->tleft, x))
	{
		Tree* f = function_form(1, u->tleft, x, L);
		return (!f)? f : join(f, NULL, u->value);
	}
	if ((trig_tok(utok) || utok == EXP_F) && ispoly(u->tleft, x))
		return function_form(1, u, x, L);
	if (utok == LN_F || utok == SQRT_F)
	{
		if (ismonomial(u->tleft, x))
		{
			map cf = polycoeffs(u->tleft, x);
			Tree* a = new_tree("A"), * v = new_tree("X");
			*L = push_back_map_if(*L, a, cf->begin->tr);
			if (cf->length > 2)
			{
				Tree* m = new_tree("M"), * vl = new_tree(tostr(cf->length - 1));
				v = join(v, vl, fnc[POW].ex);
				*L = push_back_map_if(*L, m, vl);
				clean_tree(vl);
			}
			cf = clear_map(cf);
			return join(join(a, v, fnc[PROD].ex), NULL, u->value);
		}
		Tree* tr = add_form(u->tleft, x, L);
		return (!tr) ? tr : join(tr, NULL, u->value);
	}
	if (utok == POW)
	{
		Tree* v = u->tright;
		if (!found_element(u->tleft, x) && found_element(v, x))
		{
			if (!strcmp(v->value, x))
			{
				Tree* a = new_tree("A");
				*L = push_back_map_if(*L, a, u->tleft);
				return join(a, new_tree("X"), fnc[POW].ex);
			}
			else if (ispoly(v, x))
			{
				map cf = polycoeffs(v, x);
				if (cf->length == 2)
				{
					Tree* a = new_tree("A") , * p = new_tree("P"), * q = new_tree("Q");
					*L = push_back_map_if(push_back_map_if(push_back_map_if(*L, a, u->tleft), p, cf->begin->tr), q, cf->end->tr);
					cf = clear_map(cf);
					return join(a, join(join(p, new_tree("X"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[POW].ex);
				}
				cf = clear_map(cf);
			}
		}
		if (v->tok_type == NEGATIF)
		{
			if (!strcmp(u->tleft->value, x) && strcmp(v->tleft->value, "1"))
			{
				Tree* m = new_tree("M");
				*L = push_back_map_if(*L, m, v->tleft);
				return join(new_tree("1"), join(new_tree("X"), m, fnc[POW].ex), fnc[DIVID].ex);
			}
			Tree* f = integral_form(u->tleft, x, L);
			if (f == NULL)
				return NULL;
			if (!strcmp(v->tleft->value, "1"))
				return join(new_tree("1"), f, fnc[DIVID].ex);
			Tree* n = new_tree("N");
			*L = push_back_map_if(*L, n, v->tleft);
			return join(new_tree("1"), join(f, n, fnc[POW].ex), fnc[DIVID].ex);
		}
		if (!strcmp(u->tleft->value, x))
		{
			Tree* m = new_tree("M");
			*L = push_back_map_if(*L, m, v);
			return join(new_tree("X"), m, u->value);
		}
		token tk = u->tleft->tok_type;
		if (trig_tok(tk) && ispoly(u->tleft->tleft, x))
		{
			Tree* f = function_form(1, u->tleft, x, L);
			if (!f)
				return f;
			Tree* n = (!strcmp(v->value, "2") && ACOS_F <= tk && tk <= TANH_F) ? clone(v) : new_tree("N");
			if (!strcmp(n->value, "N"))
				*L = push_back_map_if(*L, n, v);
			return join(f, n, u->value);
		}
		Tree* f = integral_form(u->tleft, x, L);
		if (f == NULL)
			return NULL;
		int j = (*L == NULL) ? 0 : (*L)->length;
		Tree* n = new_tree("N");
		*L = push_back_map_if(*L, n, v);
		if (j == (*L)->length)
		{
			clean_tree(n);
			n = new_tree("r");
			*L = push_back_map_if(*L, n, v);
		}
		return join(f, n, u->value);
	}
	if (utok == ADD || utok == SUB)
		return add_form(u, x, L);
	if (utok == PROD || utok == DIVID)
		return prod_form(u->tleft, u->tright, x, L, u->tok_type);
	return NULL;
}

static Tree* integral_table(Tree* f, const char* x)
{
	map integ_sep = separate_factor(f, x), Li = NULL;
	Tree* form = integral_form(integ_sep->end->tr, x, &Li);
	if (form == NULL)
	{
		integ_sep = clear_map(integ_sep);
		if (Li != NULL)
			Li = clear_map(Li);
		return NULL;
	}
	if (strcmp(x, "X"))
	{
		Tree* v = new_tree("X"), * w = new_tree(x);
		Li = push_back_map_if(Li, v, w);
		clean_tree(v); clean_tree(w);
	}
	string s_form = Post2in2(form);
	clean_tree(form);
	Tree* sol = form_integral(s_form, Integraltable, AMOUNT_INTEGRAL);
	free(s_form);
	if (sol != NULL)
	{
		if (Li == NULL)
		{
			sol = join(clone(integ_sep->begin->tr), sol, fnc[PROD].ex);
			integ_sep = clear_map(integ_sep);
			return sol;
		}
		Tree* ret = integral_sub(sol, &Li);
		ret = join(clone(integ_sep->begin->tr), ret, fnc[PROD].ex);
		integ_sep = clear_map(integ_sep);
		return ret;
	}
	Li = clear_map(Li);
	integ_sep = clear_map(integ_sep);
	clean_tree(sol);
	return NULL;
}

static Tree* linear_priorities(Tree* f, const char* x)
{
	if (f->tok_type == PROD)
	{
		Tree* u = f->tleft, * v = f->tright;
		if (!found_element(u, x))
		{
			Tree* s = integral(v, x);
			if (s == NULL)
				return NULL;
			return join(clone(u), s, fnc[PROD].ex);
		}
		else if (!found_element(v, x))
		{
			Tree* s = integral(u, x);
			if (s != NULL)
				return join(clone(v), s, fnc[PROD].ex);
		}
	}
	else if (f->tok_type == ADD || f->tok_type == SUB)
	{
		Tree* s = integral(f->tleft, x), * t = integral(f->tright, x);
		if (s == NULL || t == NULL)
		{
			if (s != NULL)
				clean_tree(s);
			if (t != NULL)
				clean_tree(t);
			return NULL;
		}
		return join(s, t, f->value);
	}
	return NULL;
}

static Tree* sustitution_method(Tree* f, const char* x)
{
	map P = NULL;
	P = trial_substitutions(f, P);
	if (P == NULL)
		return NULL;
	Tree* F = NULL, * v = new_tree("XX");
	mapCell* tmp = P->begin;
	while (tmp != NULL && !F)
	{
		if (!found_element(tmp->tr, x))
		{
			Tree* u = join(clone(f), diff(tmp->tr, x), fnc[DIVID].ex);
			Tree* s = simplify(substitute(u, tmp->tr, v));
			if (!found_element(s, x) && strcmp(s->value, fnc[UNDEF].ex))
				F = remplace_tree(integral(s, v->value), v->value, tmp->tr);
			clean_tree(u); clean_tree(s);
		}
		tmp = tmp->next;
	}
	P = clear_map(P);
	clean_tree(v);
	return F;
}

Tree* integrals_by_part(Tree* f, const char* x)
{
	token tk = f->tok_type;
	if (tk == DIVID)
	{
		Tree* u = f->tleft, * v = f->tright, * g = NULL;
		if (v->tok_type == PROD)
			g = join(join(clone(u), clone(v->tleft), fnc[DIVID].ex), join(new_tree("1"), clone(v->tright), fnc[DIVID].ex), fnc[PROD].ex);
		else
			g = join(clone(u), join(new_tree("1"), clone(v), fnc[DIVID].ex), fnc[PROD].ex);
		Tree* intg = integrals_by_part(g, x);
		clean_tree(g);
		return intg;
	}
	if (tk == POW && f->tright->tok_type == NEGATIF)
	{
		Tree* g = join(new_tree("1"), (!strcmp(f->tright->tleft->value, "1")) ? clone(f->tleft) : join(clone(f->tleft), clone(f->tright->tleft), fnc[POW].ex), fnc[DIVID].ex);
		Tree* intg = integrals_by_part(g, x);
		clean_tree(g);
		return intg;
	}
	if (tk == PROD)
	{
		Tree* u = f->tleft, * dv = f->tright;
		if (priority_int(u, x) < priority_int(dv, x))
		{
			u = f->tright;
			dv = f->tleft;
		}
		ipp_loop--;
		if (ipp_loop > 0)
		{
			Tree* v = integral_table(dv, x);
			if (v != NULL)
			{
				Tree* du = diff(u, x);
				Tree* s = simplify(join(clone(v), du, fnc[PROD].ex));
				Tree* ipp = integral(s, x);
				clean_tree(s);
				if (ipp != NULL)
					return join(join(clone(u), v, fnc[PROD].ex), ipp, fnc[SUB].ex);
				clean_tree(v);
			}
		}
	}
	else if (tk == LN_F || tk == ASIN_F || tk == ACOS_F || tk == SIN_F || tk == COS_F || tk == COSH_F || tk == SINH_F || tk == EXP_F)
	{
		Tree* s = join(clone(f), new_tree("1"), fnc[PROD].ex);
		Tree* q = integrals_by_part(s, x);
		clean_tree(s);
		return q;
	}
	return NULL;
}

Tree* integral(Tree* f, const char* x)
{
	Tree* F = integral_table(f, x);
	if (!F)
		F = linear_priorities(f, x);
	if (!F)
		F = sustitution_method(f, x);
	if (!F)
	{
		Tree* g = algebraic_expand(clone(f));
		if (!tree_compare(f, g))
			F = integral(g, x);
		clean_tree(g);
	}
	if (!F)
		F = integrals_by_part(f, x);
	return F;
}

struct Integral Integraltable[] =
{
	{ "1", "X", "" },
	{ "C", "C*X", "" },
	{ "X", "X^2/2", "" },
	{ "X^M", "X^(M+1)/(M+1)", "" },
	{ "sqrt(X)", "2/3*X^(3/2)", "" },
	{ "sqrt(A*X)", "2*X*sqrt(A*X)/3", "" },
	{ "1/X", "ln(X)", "" },
	{ "1/(X^M)", "~1/((M-1)*X^(M-1))", "" },
	{ "1/sqrt(X)", "2*sqrt(X)", "" },
	{ "1/sqrt(A*X)", "2*sqrt(A*X)/A", "" },
	{ "A^X", "A^X/ln(A)", "" },
	{ "A^(P*X+Q)", "A^(P*X+Q)/(P*ln(A))", "" },
	/* A*X+B */
	{ "1/(A*X+B)", "ln(A*X+B)/A", "" },
	{ "1/((A*X+B)^N)", "~1/((N-1)*A*(A*X+B)^(N-1))", "" },
	{ "X/(A*X+B)", "X/A-B/(A^2)*ln(A*X+B)", "" },
	{ "X/((A*X+B)^N)", "(~1/((N-2)*(A*X+B)^(N-2))+B/((N-1)*(A*X+B)^(N-1)))/A^2", "" },
	{ "X^M/(A*X+B)", "(X^M*(A*X+B)^(N+1))/((M+N+1)*A)-(M*B)/((M+N+1)*A)*integral(X^(M-1)/(A*X+B),X)", "" },
	{ "X^M/((A*X+B)^N)", "~X^(M+1)*(A*X+B)^(N+1)/((N+1)*B)+(M+N+2)/((N+1)*B)*integral(X^M/(A*X+B)^(N-1),X)", "" },
	{ "1/(X*(A*X+B))", "ln(X/(A*X+B))/B", "" },
	{ "(A*X+B)^N", "(A*X+B)^(N+1)/((N+1)*A)", "" },
	{ "X*(A*X+B)^N", "(A*X+B)^(N+1)*((N+1)*(A*X+B)-N-2)/(A^2*(N+1)*(N+2))", "" },
	{ "X^M*(A*X+B)^N", "(X^M*(A*X+B)^(N+1)+N*B*integral(X^(M-1)*(A*X+B)^N,X))/(A*(M+N+1))", "" },
	{ "1/((A*X+B)*(P*X+Q))", "1/(B*P-A*Q)*ln((P*X+Q)/(A*X+B))", "" },
	{ "(A*X+B)/(P*X+Q)", "(A*X)/P+(B*P-A*Q)/P^2*ln(P*X+Q)", "" },
	/* sqrt(A*X+B) */
	{ "1/sqrt(A*X+B)", "2*sqrt(A*X+B)/A", "" },
	{ "1/(X*sqrt(A*X+B))", "ln((sqrt(A*X+B)-sqrt(B))/(sqrt(A*X+B)+sqrt(B)))/sqrt(B)", "" },
	{ "sqrt(A*X+B)", "2*sqrt((A*X+B)^3)/(3*A)", "" },
	{ "X*sqrt(A*X+B)", "2*(3*A*X-2*B)/(15*A^2)*sqrt((A*X+B)^3)", "" },
	{ "sqrt(A*X+B)/X", "2*sqrt(A*X+B)+B*integral(1/(X*sqrt(A*X+B)),X)", "" },
	{ "sqrt(A*X+B)/(P*X+Q)", "(2*sqrt(A*X+B))/P+sqrt(B*P-A*Q)/(P*sqrt(P))*ln((sqrt(P*(A*X+B))-sqrt(B*P-A*Q))/(sqrt(P*(A*X+B))+sqrt(B*P-A*Q)))", "" },
	/* C+A*X^2 */
	{ "1/(C+A*X^2)", "1/(2*sqrt(~A*C))*ln((X*sqrt(A)-sqrt(~C))/(X*sqrt(A)+sqrt(~C)))", "A>0 C<0" },
	{ "1/(C+A*X^2)", "1/(2*sqrt(~A*C))*ln((X*sqrt(~A)+sqrt(C))/(X*sqrt(A)-sqrt(C)))", "A<0 C>0" },
	{ "1/(C+A*X^2)", "1/sqrt(A*C)*atan(X*sqrt(A/C))", "" },
	{ "1/((C+A*X^2)^N)", "1/(2*(N-1)*C)*X/((A*X^2+C)^(N-1))+(2*N-3)/(2*(N-1)*C)*integral(1/(C+A*X^2)^(N-1),X)", "" },
	{ "X/(C+A*X^2)", "1/(2*A)*ln(C+A*X^2)", "" },
	{ "X/((C+A*X^2)^N)", "~1/(2*A*(N-1)*(C+A*X^2)^(N-1))", "" },
	{ "X*(C+A*X^2)^N", "1/(2*A*(N+1))*(A*X^2+C)^(N+1)", "" },
	{ "X^M/(C+A*X^2)", "X^(M-1)/(A*(M-1))-C/A*integral(X^(M-2)/(C+A*X^2),X)", "" },
	{ "1/(X*(C+A*X^N))", "1/(C*N)*ln(X^N/(C+A*X^N))", "" },
	/* sqrt(C+A*X^2) */
	{ "1/(X*sqrt(C+A*X^2))", "1/(sqrt(~C)*asin(X*sqrt(~A/C)))", "C<0" },
	{ "1/(X*sqrt(C+A*X^2))", "acos(A/X)/A", "A=1 C<0" },
	{ "1/(X*sqrt(C+A*X^2))", "ln((C+sqrt(C+A*X^2))/X)", "" },
	{ "sqrt(C+A*X^2)", "X/2*sqrt(C+A*X^2)+C/(2*sqrt(A))*ln(X*sqrt(A)+sqrt(C+A*X^2))", "A>0" },
	{ "sqrt(C+A*X^2)", "X/2*sqrt(C+A*X^2)+C/(2*sqrt(~A))*asin(X*sqrt(~A/C))", "A<0" },
	{ "1/sqrt(C+A*X^2)", "ln(X*sqrt(A)+sqrt(C+A*X^2))/sqrt(A)", "A>0" },
	{ "1/sqrt(C+A*X^2)", "asin(X*sqrt(~A/C))/sqrt(~A)", "A<0" },
	{ "1/(X*sqrt(C+A*X^N))", "1/(N*sqrt(~C)*acos(sqrt(~A*X^N/C)))", "C<0" },
	{ "1/(X*sqrt(C+A*X^N))", "1/(N*sqrt(C))*ln((sqrt(C+A*X^N)-sqrt(C))/(sqrt(C+A*X^N)+sqrt(C)))", "" },
	/* A*X^2+B*X+C */
	{ "1/(A*X^2+B*X+C)", "2/sqrt(4*A*C-B^2)*atan((2*A*X+B)/sqrt(4*A*C-B^2))", "B^2<4AC" },
	{ "1/(A*X^2+B*X+C)", "1/sqrt(B^2-4*A*C)*ln(2*A*X+B-sqrt(B^2-4*A*C))/(2*A*X+B+sqrt(B^2-4*A*C))", "B^2>4AC" },
	{ "1/(A*X^2+B*X+C)", "2/(2*A*X+B)", "B^2=4AC" },
	{ "1/((A*X^2+B*X+C)^N)", "(2*A*X+B)/((N-1)*(4*A*C-B^2)*(A*X^2+B*X+C)^(N-1))+2*(2*N-1)*A/(4*A*C-B^2)*integral(1/((A*X^2+B*X+C)^(N-1)),X)", "" },
	{ "X/(A*X^2+B*X+C)", "1/(2*A)*ln(A*X^2+B*X+C)-B/(2*A)*integral(1/(A*X^2+B*X+C),X)", "" },
	{ "X^M/(A*X^2+B*X+C)", "X^(M-1)/((M-1)*A)-C/A*integral(X^(M-2)/(A*X^2+B*X+C),X)-B/A*integral(X^(M-1)/(A*X^2+B*X+C),X)", "" },
	/* sqrt(A*X^2+B*X+C) */
	{ "1/sqrt(A*X^2+B*X+C)", "1/sqrt(A)*ln(2*sqrt(A)*sqrt(A*X^2+B*X+C)+2*A*X+B)", "" },
	{ "X/sqrt(A*X^2+B*X+C)", "sqrt(A*X^2+B*X+C)/A-B/(2*A)*integral(1/sqrt(A*X^2+B*X+C),X)", "" },
	{ "sqrt(A*X^2+B*X+C)", "((2*A*X+B)*sqrt(A*X^2+B*X+C))/(4*A)+(4*A*C-B^2)/(8*A)*integral(1/sqrt(A*X^2+B*X+C),X)", "" },
	/* sin(A*X) */
	{ "sin(A*X)", "~cos(A*X)/A", "" },
	{ "X*sin(A*X)", "sin(A*X)/A^2-(X*cos(A*X))/A", "" },
	{ "1/sin(A*X)", "ln(tan(A*X)+1)/A", "" },
	{ "sin(A*X)*sin(B*X)", "sin((A-B)*X)/(2*(A-B))-sin((A+B)*X)/(2*(A+B))", "" },
	{ "X^M*sin(A*X)", "~X^M*cos(A*X)/A+M*X^(M-1)*sin(A*X)/A^2-(M*(M-1))/A^2*integral(X^(M-2)*sin(A*X),X)", "" },
	{ "sin(A*X)^N", "~sin(A*X)^(N-1)*cos(A*X)/(A*N)+(N-1)/N*integral(sin(A*X)^(N-2),X)", "" },
	{ "1/(sin(A*X)^N)", "~cos(A*X)/(A*(N-1)*sin(A*X)^(N-1))+(N-2)/(N-1)*integral(1/sin(A*X)^(N-2),X)", "" },
	/* cos(A*X) */
	{ "cos(A*X)", "sin(A*X)/A", "" },
	{ "X*cos(A*X)", "cos(A*X)/A^2+X*sin(A*X)/A", "" },
	{ "cos(A*X)*cos(B*X)", "sin((A-B)*X)/(2*(A-B))+sin((A+B)*X)/(2*(A+B))", "" },
	{ "X^M*cos(A*X)", "X^M*sin(A*X)/A+(M*X^(M-1))/A^2*cos(A*X)-(M*(M-1))/A^2*integral(X^(M-2)*cos(A*X),X)", "" },
	{ "cos(A*X)^N", "sin(A*X)*cos(A*X)^(N-1)/(A*N)+(N-1)/N*integral(cos(A*X)^(N-2),X)", "" },
	{ "1/(cos(A*X)^N)", "sin(A*X)/(A*(N-1)*cos(A*X)^(N-1))+(N-2)/(N-1)*integral(1/cos(A*X)^(N-2),X)", "" },
	/* cos(A*X) && sin(A*X) */
	{ "cos(A*X)*sin(A*X)", "sin(A*X)^2/(2*A)", "" },
	{ "cos(A*X)*sin(B*X)", "~cos((B-A)*X)/(2*(B-A))-cos((B+A)*X)/(2*(B+A))", "" },
	{ "cos(A*X)*sin(A*X)^N", "sin(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cos(A*X)^N*sin(A*X)", "~cos(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cos(A*X)^N/sin(A*X)", "cos(A*X)^(N-1)/(A*(N-1))+integral(cos(A*X)^(N-2)/sin(A*X),X)", "" },
	{ "sin(A*X)^N/cos(A*X)", "~sin(A*X)^(N-1)/(A*(N-1))+integral(sin(A*X)^(N-2)/cos(A*X),X)", "" },
	{ "cos(A*X)^M*sin(A*X)^N", "~sin(A*X)^(N-1)*cos(A*X)^(M+1)/(A*(N+M))+(N-1)/(N+M)*integral(cos(A*X)^M*sin(A*X)^(N-2),X)", "" },
	{ "sin(A*X)^M/(cos(A*X)^N)", "sin(A*X)^(M-1)/(A*(N-1)*cos(A*X)^(N-1))-(M-1)/(N-1)*integral(sin(A*X)^(M-2)/cos(A*X)^(N-2),X)", "" },
	{ "cos(A*X)^M/(sin(A*X)^N)", "~cos(A*X)^(M-1)/(A*(N-1)*sin(A*X)^(N-1))-(M-1)/(N-1)*integral(cos(A*X)^(M-2)/sin(A*X)^(N-2),X)", "" },
	/* tan(A*X) */
	{ "sin(A*X)/cos(A*X)", "~ln(cos(A*X))/A", "" },
	{ "sin(A*X)/(cos(A*X)^N)", "1/((N-1)*A*cos(A*X)^(N-1))", "" },
	{ "sin(A*X)^N/(cos(A*X)^(N+2))", "tan(A*X)^(N+1)/((N+1)*A)", "" },
	{ "sin(A*X)^N/(cos(A*X)^N)", "tan(A*X)^(N-1)/((N-1)*A)-integral(sin(A*X)^(N-2)/cos(A*X)^(N-2),X)", "" },
	/* COT(A*X) */
	{ "cos(A*X)/sin(A*X)", "ln(sin(A*X))/A", "" },
	{ "cos(A*X)/(sin(A*X)^N)", "~1/((N-1)*A*sin(A*X)^(N-1))", "" },
	{ "cos(A*X)^N/(sin(A*X)^(N+2))", "~1/((N+1)*A*tan(A*X)^(N+1))", "" },
	{ "1/(cos(A*X)*sin(A*X))", "~ln(cos(A*X)/sin(A*X))/A", "" },
	{ "cos(A*X)^N/(sin(A*X)^N)", "~(cos(A*X)^(N-1))/((N-1)*A*sin(A*X)^(N-1))-integral(cos(A*X)^(N-2)/sin(A*X)^(N-2),X)", "" },
	/* SEC(A*X) */
	{ "1/cos(A*X)", "ln(tan(A*X)+1)/A", "" },
	{ "sin(A*X)/cos(A*X)^N", "1/(N*A*cos(A*X)^N)", "" },
	/* CSC(A*X) */
	{ "cos(A*X)/(sin(A*X)^N)", "~1/(N*A*sin(A*X)^N)", "" },
	/* INVERSE TRIGO */
	{ "asin(X/A)", "X*asin(X/A)+sqrt(A^2-X^2)", "" },
	{ "asin(A*X)", "X*asin(A*X)+sqrt(1-A^2*X^2)", "" },
	{ "asin(X/A)^2", "X*asin(X/A)^2-2*X+2*sqrt(A^2-X^2)*asin(X/A)", "" },
	{ "asin(A*X)^2", "X*asin(A*X)^2-2*X+2*sqrt(1-A^2*X^2)*asin(A*X)", "" },
	{ "acos(X/A)", "X*acos(X/A)-sqrt(A^2-X^2)", "" },
	{ "acos(A*X)", "X*acos(A*X)-sqrt(1-A^2*X^2)", "" },
	{ "acos(X/A)^2", "X*acos(X/A)^2-2*X-2*sqrt(A^2-X^2)*acos(X/A)", "" },
	{ "acos(A*X)^2", "X*acos(A*X)^2-2*X-2/A*sqrt(1-A^2*X^2)*acos(A*X)", "" },
	{ "asin(X/A)/acos(X/A)", "X*asin(X/A)/acos(X/A)-A/2*ln(A^2+X^2)", "" },
	{ "asin(A*X)/acos(A*X)", "(2*A*X*asin(A*X)/acos(A*X)-ln(A^2*X^2+1))/(2*A)", "" },
	/* exp(A*X) */
	{ "exp(A*X)", "exp(A*X)/A", "" },
	{ "X*exp(A*X)", "exp(A*X)/A*(X-1/A)", "" },
	{ "X^M*exp(A*X)", "X^M*exp(A*X)/A-M/A*integral(X^(M-1)*exp(A*X),X)", "" },
	{ "exp(A*X)*sin(A*X)", "(exp(A*X)*(sin(A*X)-cos(A*X)))/(2*A)", "" },
	{ "exp(A*X)*sin(B*X)", "(exp(A*X)*(A*sin(B*X)-B*cos(B*X)))/(A^2+B^2)", "" },
	{ "cos(A*X)*exp(A*X)", "exp(A*X)*(cos(A*X)+sin(A*X))/(2*A)", "" },
	{ "cos(B*X)*exp(A*X)", "exp(A*X)*(A*cos(B*X)+B*sin(B*X))/(A^2+B^2)", "" },
	{ "cosh(A*X)*exp(A*X)", "exp(2*A*X)/(4*A)+X/2", "" },
	{ "cosh(B*X)*exp(A*X)", "exp(A*X)/(A^2-B^2)*(A*cosh(B*X)-B*sinh(B*X))", "" },
	{ "exp(A*X)*sinh(A*X)", "exp(2*A*X)/(4*A)-X/2", "" },
	{ "exp(A*X)*sinh(B*X)", "exp(A*X)/(A^2-B^2)*(A*sinh(B*X)-B*cosh(B*X))", "" },
	/* ln(A*X) */
	{ "ln(A*X)", "X*ln(A*X)-X", "" },
	{ "ln(A*X^M)", "X*ln(A*X^M)-M*X", "" },
	{ "X*ln(A*X)", "X^2/2*(ln(A*X)-1/2)", "" },
	{ "X^M*ln(A*X)", "X^(M+1)/(M+1)*(ln(A*X)-1/(M+1))", "" },
	{ "ln(A*X)/X", "ln(A*X)^2/2", "" },
	{ "ln(A*X)/(X^M)", "~ln(A*X)/((M-1)*X^(M-1))-1/((M-1)^2*X^(M-1))", "" },
	{ "ln(A*X)^N/X", "ln(A*X)^(N+1)/(N+1)", "" },
	{ "ln(A*X)^M/(X^N)", "~ln(A*X)^M/((N-1)*X^(N-1))+M/(N-1)*integral(ln(A*X)^(M-1)/(X^N),X)", "" },
	{ "1/(X*ln(A*X))", "ln(ln(A*X))", "" },
	{ "ln(A*X)^N", "X*ln(A*X)^N-N*integral(ln(A*X)^(N-1),X)", "" },
	{ "X*ln(A*X)^N", "(X^2*ln(A*X)^N)/2-N/2*integral(X*ln(A*X)^(N-1),X)", "" },
	{ "X^M*ln(A*X)^N", "(X^(M+1)*ln(A*X)^N)/(M+1)-N/(M+1)*integral(X^M*ln(A*X)^(N-1),X)", "" },
	{ "ln(A*X+B)", "(X+B/A)*ln(A*X+B)-X", "" },
	{ "X*ln(A*X+B)", "(B*X)/(2*A)-X^2/4+1/2*(X^2-B^2/A^2)*ln(A*X+B)", "" },
	{ "ln(C+A*X^2)", "(sqrt(A)*X*ln(~(A*X^2-C))-sqrt(C)*ln((sqrt(A)*X-sqrt(C))/(sqrt(A)*X+sqrt(C)))-2*sqrt(A)*X)/sqrt(A)", "A<0" },
	{ "ln(C+A*X^2)", "(sqrt(A)*X*ln(A*X^2+C)+2*(sqrt(C)*atan(sqrt(A)*X/(sqrt(C)))-sqrt(A)*X))/sqrt(A)", "" },
	{ "ln(A*X^2+B*X+C)", "1/A*sqrt(4*A*C-B^2)*atan((2*A*X)/sqrt(4*A*C-B^2))-2*X+(B/(2*A)+X)*ln(A*X^2+B*X+C)", "" },
	{ "sin(ln(A*X))", "X/2*(sin(ln(A*X))-cos(ln(A*X)))", "" },
	{ "cos(ln(A*X))", "X/2*(sin(ln(A*X))+cos(ln(A*X)))", "" },
	/* sinh(A*X) */
	{ "sinh(A*X)", "cosh(A*X)/A", "" },
	{ "X*sinh(A*X)", "X*cosh(A*X)/A-sinh(A*X)/A^2", "" },
	{ "1/sinh(A*X)", "ln(sinh(A*X)/(1+cosh(A*X)))/A", "" },
	{ "X^M*sinh(A*X)", "(X^M*cosh(A*X))/A-M/A*integral(X^(M-1)*cosh(A*X),X)", "" },
	{ "sinh(A*X)^N", "(sinh(A*X)^(N-1)*cosh(A*X))/(A*N)-(N-1)/N*integral(sinh(A*X)^(N-2),X)", "" },
	{ "1/(sinh(A*X)^N)", "~cosh(A*X)/(A*(N-1)*sinh(A*X)^(N-1))-(N-2)/(N-1)*integral(1/(sinh(A*X)^(N-2)),X)", "" },
	/* cosh(A*X) */
	{ "cosh(A*X)", "sinh(A*X)/A", "" },
	{ "X*cosh(A*X)", "X*sinh(A*X)/A-cosh(A*X)/A^2", "" },
	{ "1/cosh(A*X)", "2/A*atan(exp(A*X))", "" },
	{ "cosh(A*X)*cosh(B*X)", "sinh((A-B)*X)/(2*(A-B))+sinh((A+B)*X)/(2*(A+B))", "" },
	{ "X^M*cosh(A*X)", "(X^M*sinh(A*X))/A-M/A*integral(X^(M-1)*sinh(A*X),X)", "" },
	{ "cosh(A*X)^N", "cosh(A*X)^(N-1)*sinh(A*X)/(A*N)+(N-1)/N*integral(cosh(A*X)^(N-2),X)", "" },
	{ "1/(cosh(A*X)^N)", "sinh(A*X)/(A*(N-1)*cosh(A*X)^(N-1))+(N-2)/(N-1)*integral(1/cosh(A*X)^(N-2),X)", "" },
	/* sinh(A*X) && cosh(A*X)  */
	{ "cosh(A*X)*sinh(A*X)", "sinh(A*X)^2/(2*A)", "" },
	{ "cosh(A*X)*sinh(B*X)", "cosh((B+A)*X)/(2*(B+A))+(cosh((B-A)*X))/(2*(B-A))", "" },
	{ "cosh(A*X)*sinh(A*X)^N", "sinh(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cosh(A*X)^N*sinh(A*X)", "cosh(A*X)^(N+1)/((N+1)*A)", "" },
	/* TANH(A*X) */
	{ "sinh(A*X)/cosh(A*X)", "ln(cosh(A*X))/A", "" },
	{ "sinh(A*X)^2/(cosh(A*X)^2)", "X-sinh(A*X)/(A*cos(A*X))", "" },
	/* COTH(A*X) */
	{ "cosh(A*X)/sinh(A*X)", "ln(sinh(A*X))/A", "" },
	{ "cosh(A*X)^2/(sinh(A*X)^2)", "X-cosh(A*X)/(A*sinh(A*X))", "" },
	/* SECH(A*X) = 1/cosh */
	{ "sinh(A*X)/(cosh(A*X)^N)", "~1/((N*A)*cosh(A*X)^N)", "" },
	{ "X/(cosh(A*X)^2)", "(X*sinh(A*X))/(A*cosh(A*X))-ln(cosh(A*X))/A^2", "" },
	/* CSCH(A*X) = 1/sinh */
	{ "cosh(A*X)/(sinh(A*X)^N)", "~1/(N*A*sinh(A*X)^N)", "" },
	{ "X/(sinh(A*X)^2)", "~X*cosh(A*X)/(A*sinh(A*X))+ln(sinh(A*X))/A^2", "" },
	/* INVERSE TRIGO HYPERBOLIQUE */
	{ "asinh(X/A)", "X*asinh(X/A)-sqrt(A^2+X^2)", "" },
	{ "asinh(A*X)", "X*asinh(A*X)-sqrt(1+A^2*X^2)/A", "" },
	{ "acosh(X/A)", "X*acosh(X/A)-A*sqrt((~1+X/A)*(1+X/A))", "" },
	{ "acosh(A*X)", "X*acosh(A*X)-sqrt((~1+A*X)*(1+A*X))/A", "" },
	/* TRIGONOMETRIQUE & HYPERBOLIQUE */
	{ "cos(A*X)*cosh(B*X)", "(A*sin(A*X)*cosh(B*X)+B*cos(A*X)*sinh(B*X))/(A^2+B^2)", "" },
	{ "cos(A*X)*sinh(B*X)", "(A*sin(A*X)*sinh(B*X)+B*cos(A*X)*cosh(B*X))/(A^2+B^2)", "" },
	{ "sin(A*X)*sinh(B*X)", "(B*sin(A*X)*sinh(B*X)-B*cos(A*X)*cosh(B*X))/(A^2+B^2)", "" },
	{ "sin(A*X)*sinh(B*X)", "(B*sin(A*X)*cosh(B*X)-A*cos(A*X)*sinh(B*X))/(A^2+B^2)", "" }
};

