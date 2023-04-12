#include "integral.h"

#define AMOUNT_INTEGRAL 166
#define AMOUNT_DERIV 19
int ipp_loop = 10;
char int_cond[10] = { 0 };

static Tree* integral_form(Tree* u, const char* x, map* L);

static map separate_factor(Tree* u, const char* x)
{
	map L = NULL;
	if (!found_element(u, x))
	{
		Tree* un = new_tree("1");
		L = push_back_map(push_back_map(L, u), un);
		clean_tree(un);
		return L;
	}
	if (u->tok_type == DIVID)
	{
		map f = separate_factor(u->tleft, x), g = separate_factor(u->tright, x);
		Tree* free_of_part = join(clone(f->begin->tr), clone(g->begin->tr), fnc[DIVID].ex);
		Tree* dependent_part = join(clone(f->end->tr), clone(g->end->tr), fnc[DIVID].ex);
		f = clear_map(f); g = clear_map(g);
		L = push_back_map(push_back_map(L, free_of_part), dependent_part);
		clean_tree(free_of_part);
		clean_tree(dependent_part);
		return L;
	}
	if (u->tok_type == PROD)
	{
		Tree* free_of_part = NULL, * dependent_part = NULL;
		for (int i = 1; i <= nb_operand(u); i++)
		{
			map f = separate_factor(operand(u, i), x);
			free_of_part = (free_of_part == NULL) ? clone(f->begin->tr) : join(free_of_part, clone(f->begin->tr), fnc[u->tok_type].ex);
			dependent_part = (dependent_part == NULL) ? clone(f->end->tr) : join(dependent_part, clone(f->end->tr), fnc[u->tok_type].ex);
			f = clear_map(f);
		}
		if (free_of_part == NULL)
			free_of_part = new_tree("1");
		if (dependent_part == NULL)
			dependent_part = new_tree("1");
		L = push_back_map(push_back_map(L, free_of_part), dependent_part);
		clean_tree(free_of_part);
		clean_tree(dependent_part);
		return L;
	}
	Tree* un = new_tree("1");
	L = push_back_map(push_back_map(L, un), u);
	clean_tree(un);
	return L;
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
	cf = push_back_map(cf, r);
	clean_tree(r);
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
	{ fnc[NEGATIF].ex, "u", "" },
	{ fnc[LN_F].ex, "u/U", "" },
	{ fnc[LOG_F].ex, "u/(U*ln(10))", "" },
	{ fnc[EXP_F].ex, "u*exp(U)", "" },
	{ fnc[ABS_F].ex, "u*sign(U)", "" },
	{ fnc[SQRT_F].ex, "u/(2*sqrt(U))", "" },
	{ fnc[COS_F].ex, "~u*sin(U)", "" },
	{ fnc[SIN_F].ex, "u*cos(U)", "" },
	{ fnc[TAN_F].ex, "u/cos(U)^2", "" },
	{ fnc[COSH_F].ex, "u*sinh(U)", "" },
	{ fnc[SINH_F].ex, "u*cosh(U)", "" },
	{ fnc[TANH_F].ex, "u/cosh(U)^2", "" },
	{ fnc[ACOS_F].ex, "~u/sqrt(1-U^2)", "" },
	{ fnc[ASIN_F].ex, "u/sqrt(1-U^2)", "" },
	{ fnc[ATAN_F].ex, "u/(U^2+1)", "" },
	{ fnc[ACOSH_F].ex, "u/sqrt(U^2-1)", "" },
	{ fnc[ASINH_F].ex, "u/sqrt(1+U^2)", "" },
	{ fnc[ATANH_F].ex, "u/(1-U^2)", "" },
	{ fnc[CBRT_F].ex, "u/(3*U^(2/3))", "" }
};

static Tree* subderiv(Tree* u, const char* v, Tree* w)
{
	Tree* y = remplace_tree(u, v, w);
	clean_tree(u);
	return y;
}

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
		if (tok == PROD)
		{
			Tree* w = denominator_fun(tr);
			if (found_element(w, vr))
			{
				Tree* v = numerator_fun(tr);
				Tree* dl = diff(v, vr), * dr = diff(w, vr);
				return join(join(join(dl, clone(w), fnc[PROD].ex), join(dr, v, fnc[PROD].ex), fnc[SUB].ex), join(w, new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
			}
			clean_tree(w);
		}
		Tree* dl = diff(tr->tleft, vr), * dr = diff(tr->tright, vr);
		if (tok == ADD || tok == SUB)
			return simplify(join(dl, dr, sig));
		if (tok == PROD || tok == DIVID)
		{
			Tree* t = simplify(join(join(dl, clone(tr->tright), fnc[PROD].ex), join(dr, clone(tr->tleft), fnc[PROD].ex), fnc[(tok == PROD) ? ADD : SUB].ex));
			return (tok == PROD)? t : join(t, join(clone(tr->tright), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);;
		}
		if (tok == POW)
		{
			Tree* sol = NULL;
			bool v = !strcmp(dr->value, "0");
			if (v || !strcmp(dl->value, "0"))
				sol = subderiv(subderiv(subderiv(to_tree(In2post2(v ? "c*u*U^(c-1)" : "ln(c)*c^U")), "U", v ? tr->tleft : tr->tright), "u", v ? dl : dr), "c", v ? tr->tright : tr->tleft);
			else
				sol = subderiv(subderiv(subderiv(subderiv(to_tree(In2post2("(u*V/U+ln(U)*v)*U^V")), "U", tr->tleft), "V", tr->tright), "u", dl), "v", dr);
			clean_tree(dr); clean_tree(dl);
			return sol;
		}
	}
	else if (op == FUNCTION || op == NEGATION)
	{
		if (tok == INTEGRAL_F)
		{
			Tree* t = tr;
			while (t->tleft->tok_type == SEPARATEUR)
				t = t->tleft;
			return clone(t->tleft);
		}
		if (tok == LOGBASE_F || tok == ROOT_F)
		{
			Tree* dl = simplify(diff(tr->tleft->tleft, vr)), * sol = to_tree(In2post2((tok == LOGBASE_F) ? "u/(U*ln(c))" : "u/(c*U^((c-1)/c))"));
			sol = subderiv(subderiv(subderiv(sol, "U", tr->tleft->tleft), "u", dl), "u", tr->tleft->tright);
			clean_tree(dl);
			return sol;
		}
		Tree* dl = simplify(diff(tr->tleft, vr));
		Tree* sol = form_integral(sig, Derivtable, AMOUNT_DERIV);
		if (sol != NULL)
		{
			sol = subderiv(subderiv(sol, "U", tr->tleft), "u", dl);
			clean_tree(dl);
			return sol;
		}
		clean_tree(dl);
	}
	return join(join(clone(tr), new_tree(vr), fnc[SEPARATEUR].ex), NULL, fnc[DERIV_F].ex);
}

/* primitive */

static Tree* function_form(int var, Tree* u, const char* x, map* L)
{
	map cf1 = polycoeffs(u->tleft, x);
	if (cf1->length == 2)
	{
		Tree* a = new_tree((var == 1) ? "a" : "b");
		if (!ismonomial(u->tleft, x))
		{
			Tree* b = join(clone(a), new_tree("x"), fnc[PROD].ex);
			*L = push_back_map_if(*L, b, u->tleft);
		}
		Tree* tr = cf1->begin->tr;
		token tk = u->tok_type;
		if (((ACOS_F <= tk && tk <= ATAN_F) || (ACOSH_F <= tk && tk <= ATANH_F)) && tr->tok_type == DIVID && !strcmp(tr->tleft->value, "1"))
		{
			*L = push_back_map_if(*L, a, tr->tright);
			cf1 = clear_map(cf1);
			return join(join(new_tree("x"), a, fnc[DIVID].ex), NULL, u->value);
		}
		*L = push_back_map_if(*L, a, tr);
		cf1 = clear_map(cf1);
		return join(join(a, new_tree("x"), fnc[PROD].ex), NULL, u->value);
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
			Tree* a = new_tree("a"), * b = new_tree("b");
			*L = push_back_map_if(*L, a, coefs->begin->tr);
			if (k == (*L)->length)
			{
				clean_tree(a); clean_tree(b);
				a = new_tree("p"); b = new_tree("q");
			}
			*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->end->tr);
			coefs = clear_map(coefs);
			return join(join(a, new_tree("x"), fnc[PROD].ex), b, fnc[ADD].ex);
		}

		if (ismonomial(u->tleft, x) && ismonomial(u->tright, x))
		{
			if (strcmp(coefs->begin->next->tr->value, "0"))
			{
				int k = coefs->length - 2;
				Tree* a = new_tree("a"), * b = new_tree("b");
				*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->begin->next->tr);
				coefs = clear_map(coefs);
				if (k == 1)
					return join(new_tree("x"), join(join(a, new_tree("x"), fnc[PROD].ex), b, fnc[ADD].ex), fnc[PROD].ex);
				Tree* m = new_tree("m"), * m_value = new_tree(tostr(k));
				*L = push_back_map_if(*L, m, m_value);
				clean_tree(m_value);
				Tree* q = join(new_tree("x"), m, fnc[POW].ex);
				return join(q, join(join(a, new_tree("x"), fnc[PROD].ex), b, fnc[ADD].ex), fnc[PROD].ex);
			}
			if (strcmp(coefs->begin->tr->value, "0") && strcmp(coefs->end->tr->value, "0"))
			{
				int k = coefs->length;
				Tree* a = new_tree("a"), * c = new_tree("c"), * n = new_tree((k == 3) ? "2" : "n");
				if (k > 3)
				{
					Tree* val = new_tree(tostr(k - 1));
					*L = push_back_map_if(*L, n, val);
					clean_tree(val);
				}
				*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), c, coefs->end->tr);
				sprintf(int_cond, "a%s0 c%s0", (coefs->begin->tr->tok_type == NEGATIF) ? "<" : ">", (coefs->end->tr->tok_type == NEGATIF) ? "<" : ">");
				coefs = clear_map(coefs);
				return join(c, join(a, join(new_tree("x"), n, fnc[POW].ex), fnc[PROD].ex), fnc[ADD].ex);
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
					Tree* a = new_tree("a"), * b = new_tree("b"), * n = new_tree("n");
					*L = push_back_map_if(push_back_map_if(push_back_map_if(*L, n, fct->tright), a, coefs->begin->tr), b, coefs->end->tr);
					coefs = clear_map(coefs);
					return join(join(join(a, new_tree("x"), fnc[PROD].ex), b, fnc[ADD].ex), n, fnc[POW].ex);
				}
				if (fct->tok_type == PROD && (fct->tleft->tok_type == ADD || fct->tleft->tok_type == SUB) && (fct->tright->tok_type == ADD || fct->tright->tok_type == SUB))
				{
					coefs = clear_map(coefs);
					map cfs = polycoeffs(fct->tright, x);
					coefs = polycoeffs(fct->tleft, x);
					Tree* a = new_tree("a"), * b = new_tree("b"), * p = new_tree("p"), * q = new_tree("q");
					*L = push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->end->tr);
					*L = push_back_map_if(push_back_map_if(*L, p, cfs->begin->tr), q, cfs->end->tr);
					coefs = clear_map(coefs); cfs = clear_map(cfs);
					return join(join(join(a, new_tree("x"), fnc[PROD].ex), b, fnc[ADD].ex), join(join(p, new_tree("x"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[PROD].ex);
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
					strcpy(int_cond, "b^2>4ac");
				else if (n == 0)
					strcpy(int_cond, "b^2=4ac");
				else
					strcpy(int_cond, "b^2<4ac");
			}
			else
				strcpy(int_cond, "b^2>4ac");
			clean_tree(t);
			Tree* a = new_tree("a"), * b = new_tree("b"), * c = new_tree("c");
			*L = push_back_map_if(push_back_map_if(push_back_map_if(*L, a, coefs->begin->tr), b, coefs->end->back->tr), c, coefs->end->tr);
			coefs = clear_map(coefs);
			a = join(a, join(new_tree("x"), new_tree("2"), fnc[POW].ex), fnc[PROD].ex);
			b = join(b, new_tree("x"), fnc[PROD].ex);
			return join(join(a, b, fnc[ADD].ex), c, fnc[ADD].ex);
		}
		coefs = clear_map(coefs);
	}
	Tree* f = integral_form(u->tleft, x, L), * g = integral_form(u->tright, x, L);
	if (f == NULL || g == NULL)
	{
		if (f != NULL)
			clean_tree(f);
		if (g != NULL)
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
			Tree* n = (!strcmp(u->tright->value, "2") && ((tk == SINH_F && tk0 == COSH_F) || (tk0 == SINH_F && tk == COSH_F))) ? clone(u->tright) : new_tree("n");
			if (!strcmp(n->value, "n"))
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
				Tree* n = new_tree("n");
				*L = push_back_map_if(*L, n, u->tright);
				return join(join(g, n, fnc[POW].ex), join(h, join(n, new_tree("2"), fnc[ADD].ex), fnc[POW].ex), fnc[op].ex);
			}
			clean_tree(f);
		}
		Tree* m = new_tree("m"), * n = new_tree("n");
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
			if (f != NULL)
				clean_tree(f);
			if (g != NULL)
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
		Tree* n = new_tree("n");
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
		Tree* n = new_tree("n");
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
				Tree* p = new_tree("p"), * q = new_tree("q");
				*L = push_back_map_if(push_back_map_if(*L, p, cf->begin->tr), q, cf->end->tr);
				cf = clear_map(cf); clean_tree(dg);
				dg = join(join(p, new_tree("x"), fnc[PROD].ex), q, fnc[ADD].ex);
				return join(dg, f, fnc[op].ex);
			}
			return join(new_tree("x"), f, fnc[op].ex);
		}
		if (ismonomial(u, x))
		{
			Tree* m = new_tree("m");
			*L = push_back_map_if(*L, m, dg);
			clean_tree(dg);
			return join(join(new_tree("x"), m, fnc[POW].ex), f, fnc[op].ex);
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
				Tree* p = new_tree("p"), * q = new_tree("q");
				*L = push_back_map_if(push_back_map_if(*L, p, cf->begin->tr), q, cf->end->tr);
				cf = clear_map(cf);
				dg = join(join(p, new_tree("x"), fnc[PROD].ex), q, fnc[ADD].ex);
				return join(f, dg, fnc[op].ex);
			}
			return join(f, new_tree("x"), fnc[op].ex);
		}
		if (ismonomial(v, x))
		{
			Tree* m = new_tree("m");
			*L = push_back_map_if(*L, m, dg);
			clean_tree(dg);
			if (op == PROD)
				return join(join(new_tree("x"), m, fnc[POW].ex), f, fnc[op].ex);
			return join(f, join(new_tree("x"), m, fnc[POW].ex), fnc[op].ex);
		}
		clean_tree(dg);
	}
	if (ispoly(u, x) && ispoly(v, x))
	{
		map cf = polycoeffs(u, x), cf1 = polycoeffs(v, x);
		if (cf->length == 2 && cf1->length == 2)
		{
			Tree* a = new_tree("a"), * b = new_tree("b"), * p = new_tree("p"), * q = new_tree("q");
			*L = push_back_map_if(push_back_map_if(*L, p, cf1->begin->tr), q, cf1->end->tr);
			*L = push_back_map_if(push_back_map_if(*L, a, cf->begin->tr), b, cf->end->tr);
			cf = clear_map(cf); cf1 = clear_map(cf1);
			return join(join(join(a, new_tree("x"), fnc[PROD].ex), b, fnc[ADD].ex), join(join(p, new_tree("x"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[op].ex);
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
		Tree* c = new_tree("c");
		*L = push_back_map_if(*L, c, v);
		clean_tree(v);
		return c;
	}
	if (!strcmp(u->value, x))
		return new_tree("x");
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
			Tree* a = new_tree("a"), * v = new_tree("x");
			*L = push_back_map_if(*L, a, cf->begin->tr);
			if (cf->length > 2)
			{
				Tree* m = new_tree("m"), * vl = new_tree(tostr(cf->length - 1));
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
				Tree* a = new_tree("a");
				*L = push_back_map_if(*L, a, u->tleft);
				return join(a, new_tree("x"), fnc[POW].ex);
			}
			else if (ispoly(v, x))
			{
				map cf = polycoeffs(v, x);
				if (cf->length == 2)
				{
					Tree* a = new_tree("a") , * p = new_tree("p"), * q = new_tree("q");
					*L = push_back_map_if(push_back_map_if(push_back_map_if(*L, a, u->tleft), p, cf->begin->tr), q, cf->end->tr);
					cf = clear_map(cf);
					return join(a, join(join(p, new_tree("x"), fnc[PROD].ex), q, fnc[ADD].ex), fnc[POW].ex);
				}
				cf = clear_map(cf);
			}
		}
		if (v->tok_type == NEGATIF)
		{
			if (!strcmp(u->tleft->value, x) && strcmp(v->tleft->value, "1"))
			{
				Tree* m = new_tree("m");
				*L = push_back_map_if(*L, m, v->tleft);
				return join(new_tree("1"), join(new_tree("x"), m, fnc[POW].ex), fnc[DIVID].ex);
			}
			Tree* f = integral_form(u->tleft, x, L);
			if (f == NULL)
				return NULL;
			if (!strcmp(v->tleft->value, "1"))
				return join(new_tree("1"), f, fnc[DIVID].ex);
			Tree* n = new_tree("n");
			*L = push_back_map_if(*L, n, v->tleft);
			return join(new_tree("1"), join(f, n, fnc[POW].ex), fnc[DIVID].ex);
		}
		if (!strcmp(u->tleft->value, x))
		{
			Tree* m = new_tree("m");
			*L = push_back_map_if(*L, m, v);
			return join(new_tree("x"), m, u->value);
		}
		token tk = u->tleft->tok_type;
		if (trig_tok(tk) && ispoly(u->tleft->tleft, x))
		{
			Tree* f = function_form(1, u->tleft, x, L);
			if (!f)
				return f;
			Tree* n = (!strcmp(v->value, "2") && ACOS_F <= tk && tk <= TANH_F) ? clone(v) : new_tree("n");
			if (!strcmp(n->value, "n"))
				*L = push_back_map_if(*L, n, v);
			return join(f, n, u->value);
		}
		Tree* f = integral_form(u->tleft, x, L);
		if (f == NULL)
			return NULL;
		int j = (*L == NULL) ? 0 : (*L)->length;
		Tree* n = new_tree("n");
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
	if (strcmp(x, "x"))
	{
		Tree* v = new_tree("x"), * w = new_tree(x);
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
	{ "1", "x", "" },
	{ "c", "c*x", "" },
	{ "x", "x^2/2", "" },
	{ "x^m", "x^(m+1)/(m+1)", "" },
	{ "sqrt(x)", "2/3*x^(3/2)", "" },
	{ "sqrt(a*x)", "2*x*sqrt(a*x)/3", "" },
	{ "1/x", "ln(x)", "" },
	{ "1/(x^m)", "~1/((m-1)*x^(m-1))", "" },
	{ "1/sqrt(x)", "2*sqrt(x)", "" },
	{ "1/sqrt(a*x)", "2*sqrt(a*x)/a", "" },
	{ "a^x", "a^x/ln(a)", "" },
	{ "a^(p*x+q)", "a^(p*x+q)/(p*ln(a))", "" },
	/* a*x+b */
	{ "1/(a*x+b)", "ln(a*x+b)/a", "" },
	{ "1/((a*x+b)^n)", "~1/((n-1)*a*(a*x+b)^(n-1))", "" },
	{ "x/(a*x+b)", "x/a-b/(a^2)*ln(a*x+b)", "" },
	{ "x/((a*x+b)^n)", "(~1/((n-2)*(a*x+b)^(n-2))+b/((n-1)*(a*x+b)^(n-1)))/a^2", "" },
	{ "x^m/(a*x+b)", "(x^m*(a*x+b)^(n+1))/((m+n+1)*a)-(m*b)/((m+n+1)*a)*integral(x^(m-1)/(a*x+b),x)", "" },
	{ "x^m/((a*x+b)^n)", "~x^(m+1)*(a*x+b)^(n+1)/((n+1)*b)+(m+n+2)/((n+1)*b)*integral(x^m/(a*x+b)^(n-1),x)", "" },
	{ "1/(x*(a*x+b))", "ln(x/(a*x+b))/b", "" },
	{ "(a*x+b)^n", "(a*x+b)^(n+1)/((n+1)*a)", "" },
	{ "x^m*(a*x+b)^n", "(x^m*(a*x+b)^(n+1)+n*b*integral(x^(m-1)*(a*x+b)^n,x))/(a*(m+n+1))", "" },
	{ "1/((a*x+b)*(p*x+q))", "1/(b*p-a*q)*ln((p*x+q)/(a*x+b))", "" },
    { "(a*x+b)/(p*x+q)", "(a*x)/p+(b*p-a*q)/p^2*ln(p*x+q)", "" },
	/* sqrt(a*x+b) */
	{ "1/sqrt(a*x+b)", "2*sqrt(a*x+b)/a", "" },
	{ "1/(x*sqrt(a*x+b))", "ln((sqrt(a*x+b)-sqrt(b))/(sqrt(a*x+b)+sqrt(b)))/sqrt(b)", "" },
	{ "sqrt(a*x+b)", "2*sqrt((a*x+b)^3)/(3*a)", "" },
	{ "x*sqrt(a*x+b)", "2*(3*a*x-2*b)/(15*a^2)*sqrt((a*x+b)^3)", "" },
	{ "sqrt(a*x+b)/x", "2*sqrt(a*x+b)+b*integral(1/(x*sqrt(a*x+b)),x)", "" },
	{ "sqrt(a*x+b)/(p*x+q)", "(2*sqrt(a*x+b))/p+sqrt(b*p-a*q)/(p*sqrt(p))*ln((sqrt(p*(a*x+b))-sqrt(b*p-a*q))/(sqrt(p*(a*x+b))+sqrt(b*p-a*q)))", "" },
	{ "sqrt(a*x+b)/sqrt(p*x+q)", "sqrt((a*x+b)*(p*x+q))/a+(q*a-p*b)/(2*a)*integral(1/(sqrt((a*x+b)*(p*x+q))),x)", "" },
	/* c+a*x^2 */
	{ "1/(c+a*x^2)", "1/(2*sqrt(~a*c))*ln((x*sqrt(a)-sqrt(~c))/(x*sqrt(a)+sqrt(~c)))", "a>0 c<0" },
	{ "1/(c+a*x^2)", "1/(2*sqrt(~a*c))*ln((x*sqrt(~a)+sqrt(c))/(x*sqrt(a)-sqrt(c)))", "a<0 c>0" },
	{ "1/(c+a*x^2)", "1/sqrt(a*c)*atan(x*sqrt(a/c))", "" },
	{ "1/((c+a*x^2)^n)", "1/(2*(n-1)*c)*x/((a*x^2+c)^(n-1))+(2*n-3)/(2*(n-1)*c)*integral(1/(c+a*x^2)^(n-1),x)", "" },
	{ "x/(c+a*x^2)", "1/(2*a)*ln(c+a*x^2)", "" },
	{ "x/((c+a*x^2)^n)", "~1/(2*a*(n-1)*(c+a*x^2)^(n-1))", "" },
	{ "x*(c+a*x^2)^n", "1/(2*a*(n+1))*(a*x^2+c)^(n+1)", "" },
	{ "x^m/(c+a*x^2)", "x^(m-1)/(a*(m-1))-c/a*integral(x^(m-2)/(c+a*x^2),x)", "" },
	{ "1/(x*(c+a*x^n))", "1/(c*n)*ln(x^n/(c+a*x^n))", "" },
	{ "1/(x*sqrt(c+a*x^n))", "1/(n*sqrt(c))*ln((sqrt(c+a*x^n)-sqrt(c))/(sqrt(c+a*x^n)+sqrt(c)))", "c>0" },
	{ "1/(x*sqrt(c+a*x^n))", "1/(n*sqrt(~c)*acos(sqrt(~a*x^n/c)))", "c<0" },
	/* sqrt(c+a*x^2) */
	{ "1/(x*sqrt(c+a*x^2))", "1/(sqrt(~c)*asin(x*sqrt(~a/c)))", "c<0" },
	{ "1/(x*sqrt(c+a*x^2))", "acos(a/x)/a", "a=1 c<0" },
	{ "1/(x*sqrt(c+a*x^2))", "ln((c+sqrt(c+a*x^2))/x)", "" },
	{ "sqrt(c+a*x^2)", "x/2*sqrt(c+a*x^2)+c/(2*sqrt(a))*ln(x*sqrt(a)+sqrt(c+a*x^2))", "a>0" },
	{ "sqrt(c+a*x^2)", "x/2*sqrt(c+a*x^2)+c/(2*sqrt(~a))*asin(x*sqrt(~a/c))", "a<0" },
	{ "1/sqrt(c+a*x^2)", "ln(x*sqrt(a)+sqrt(c+a*x^2))/sqrt(a)", "a>0" },
	{ "1/sqrt(c+a*x^2)", "asin(x*sqrt(~a/c))/sqrt(~a)", "a<0" },
	{ "1/(x*sqrt(c+a*x^n))", "1/(n*sqrt(~c)*acos(sqrt(~a*x^n/c)))", "c<0" },
	{ "1/(x*sqrt(c+a*x^n))", "1/(n*sqrt(c))*ln((sqrt(c+a*x^n)-sqrt(c))/(sqrt(c+a*x^n)+sqrt(c)))", "" },
	/* a*x^2+b*x+c */
	{ "1/(a*x^2+b*x+c)", "2/sqrt(4*a*c-b^2)*atan((2*a*x+b)/sqrt(4*a*c-b^2))", "b^2<4ac" },
	{ "1/(a*x^2+b*x+c)", "1/sqrt(b^2-4*a*c)*ln(2*a*x+b-sqrt(b^2-4*a*c))/(2*a*x+b+sqrt(b^2-4*a*c))", "b^2>4ac" },
	{ "1/(a*x^2+b*x+c)", "2/(2*a*x+b)", "b^2=4ac" },
	{ "1/((a*x^2+b*x+c)^n)", "(2*a*x+b)/((n-1)*(4*a*c-b^2)*(a*x^2+b*x+c)^(n-1))+2*(2*n-1)*a/(4*a*c-b^2)*integral(1/((a*x^2+b*x+c)^(n-1)),x)", "" },
	{ "x/(a*x^2+b*x+c)", "1/(2*a)*ln(a*x^2+b*x+c)-b/(2*a)*integral(1/(a*x^2+b*x+c),x)", "" },
	{ "x^m/(a*x^2+b*x+c)", "x^(m-1)/((m-1)*a)-c/a*integral(x^(m-2)/(a*x^2+b*x+c),x)-b/a*integral(x^(m-1)/(a*x^2+b*x+c),x)", "" },
	/* sqrt(a*x^2+b*x+c) */
	{ "1/sqrt(a*x^2+b*x+c)", "1/sqrt(a)*ln(2*sqrt(a)*sqrt(a*x^2+b*x+c)+2*a*x+b)", "" },
	{ "x/sqrt(a*x^2+b*x+c)", "sqrt(a*x^2+b*x+c)/a-b/(2*a)*integral(1/sqrt(a*x^2+b*x+c),x)", "" },
	{ "sqrt(a*x^2+b*x+c)", "((2*a*x+b)*sqrt(a*x^2+b*x+c))/(4*a)+(4*a*c-b^2)/(8*a)*integral(1/sqrt(a*x^2+b*x+c),x)", "" },
	/* sin(a*x) */
	{ "sin(a*x)", "~cos(a*x)/a", "" },
	{ "x*sin(a*x)", "sin(a*x)/a^2-(x*cos(a*x))/a", "" },
	{ "1/sin(a*x)", "ln(tan(a*x)+1)/a", "" },
	{ "sin(a*x)*sin(b*x)", "sin((a-b)*x)/(2*(a-b))-sin((a+b)*x)/(2*(a+b))", "" },
	{ "x^m*sin(a*x)", "~x^m*cos(a*x)/a+m*x^(m-1)*sin(a*x)/a^2-(m*(m-1))/a^2*integral(x^(m-2)*sin(a*x),x)", "" },
	{ "sin(a*x)^n", "~sin(a*x)^(n-1)*cos(a*x)/(a*n)+(n-1)/n*integral(sin(a*x)^(n-2),x)", "" },
	{ "1/(sin(a*x)^n)", "~cos(a*x)/(a*(n-1)*sin(a*x)^(n-1))+(n-2)/(n-1)*integral(1/sin(a*x)^(n-2),x)", "" },
	/* cos(a*x) */
	{ "cos(a*x)", "sin(a*x)/a", "" },
	{ "x*cos(a*x)", "cos(a*x)/a^2+x*sin(a*x)/a", "" },
	{ "cos(a*x)*cos(b*x)", "sin((a-b)*x)/(2*(a-b))+sin((a+b)*x)/(2*(a+b))", "" },
	{ "x^m*cos(a*x)", "x^m*sin(a*x)/a+(m*x^(m-1))/a^2*cos(a*x)-(m*(m-1))/a^2*integral(x^(m-2)*cos(a*x),x)", "" },
	{ "cos(a*x)^n", "sin(a*x)*cos(a*x)^(n-1)/(a*n)+(n-1)/n*integral(cos(a*x)^(n-2),x)", "" },
	{ "1/(cos(a*x)^n)", "sin(a*x)/(a*(n-1)*cos(a*x)^(n-1))+(n-2)/(n-1)*integral(1/cos(a*x)^(n-2),x)", "" },
	/* cos(a*x) && sin(a*x) */
	{ "cos(a*x)*sin(a*x)", "sin(a*x)^2/(2*a)", "" },
	{ "cos(a*x)*sin(b*x)", "~cos((b-a)*x)/(2*(b-a))-cos((b+a)*x)/(2*(b+a))", "" },
	{ "cos(a*x)*sin(a*x)^n", "sin(a*x)^(n+1)/((n+1)*a)", "" },
	{ "cos(a*x)^n*sin(a*x)", "~cos(a*x)^(n+1)/((n+1)*a)", "" },
	{ "cos(a*x)^n/sin(a*x)", "cos(a*x)^(n-1)/(a*(n-1))+integral(cos(a*x)^(n-2)/sin(a*x),x)", "" },
	{ "sin(a*x)^n/cos(a*x)", "~sin(a*x)^(n-1)/(a*(n-1))+integral(sin(a*x)^(n-2)/cos(a*x),x)", "" },
	{ "cos(a*x)^m*sin(a*x)^n", "~sin(a*x)^(n-1)*cos(a*x)^(m+1)/(a*(n+m))+(n-1)/(n+m)*integral(cos(a*x)^m*sin(a*x)^(n-2),x)", "" },
	{ "sin(a*x)^m/(cos(a*x)^n)", "sin(a*x)^(m-1)/(a*(n-1)*cos(a*x)^(n-1))-(m-1)/(n-1)*integral(sin(a*x)^(m-2)/cos(a*x)^(n-2),x)", "" },
	{ "cos(a*x)^m/(sin(a*x)^n)", "~cos(a*x)^(m-1)/(a*(n-1)*sin(a*x)^(n-1))-(m-1)/(n-1)*integral(cos(a*x)^(m-2)/sin(a*x)^(n-2),x)", "" },
	/* tan(a*x) */
	{ "sin(a*x)/cos(a*x)", "~ln(cos(a*x))/a", "" },
	{ "sin(a*x)/(cos(a*x)^n)", "1/((n-1)*a*cos(a*x)^(n-1))", "" },
	{ "sin(a*x)^n/(cos(a*x)^(n+2))", "tan(a*x)^(n+1)/((n+1)*a)", "" },
	{ "sin(a*x)^n/(cos(a*x)^n)", "tan(a*x)^(n-1)/((n-1)*a)-integral(sin(a*x)^(n-2)/cos(a*x)^(n-2),x)", "" },
	/* cot(a*x) */
	{ "cos(a*x)/sin(a*x)", "ln(sin(a*x))/a", "" },
	{ "cos(a*x)/(sin(a*x)^n)", "~1/((n-1)*a*sin(a*x)^(n-1))", "" },
	{ "cos(a*x)^n/(sin(a*x)^(n+2))", "~1/((n+1)*a*tan(a*x)^(n+1))", "" },
	{ "1/(cos(a*x)*sin(a*x))", "~ln(cos(a*x)/sin(a*x))/a", "" },
	{ "cos(a*x)^n/(sin(a*x)^n)", "~(cos(a*x)^(n-1))/((n-1)*a*sin(a*x)^(n-1))-integral(cos(a*x)^(n-2)/sin(a*x)^(n-2),x)", "" },
	/* sec(a*x) */
	{ "1/cos(a*x)", "ln(tan(a*x)+1)/a", "" },
	{ "sin(a*x)/cos(a*x)^n", "1/(n*a*cos(a*x)^n)", "" },
	/* csc(a*x) */
	{ "cos(a*x)/(sin(a*x)^n)", "~1/(n*a*sin(a*x)^n)", "" },
	/* inverse trigo */
	{ "asin(x/a)", "x*asin(x/a)+sqrt(a^2-x^2)", "" },
	{ "asin(a*x)", "x*asin(a*x)+sqrt(1-a^2*x^2)", "" },
	{ "asin(x/a)^2", "x*asin(x/a)^2-2*x+2*sqrt(a^2-x^2)*asin(x/a)", "" },
	{ "asin(a*x)^2", "x*asin(a*x)^2-2*x+2*sqrt(1-a^2*x^2)*asin(a*x)", "" },
	{ "acos(x/a)", "x*acos(x/a)-sqrt(a^2-x^2)", "" },
	{ "acos(a*x)", "x*acos(a*x)-sqrt(1-a^2*x^2)", "" },
	{ "acos(x/a)^2", "x*acos(x/a)^2-2*x-2*sqrt(a^2-x^2)*acos(x/a)", "" },
	{ "acos(a*x)^2", "x*acos(a*x)^2-2*x-2/a*sqrt(1-a^2*x^2)*acos(a*x)", "" },
	{ "asin(x/a)/acos(x/a)", "x*asin(x/a)/acos(x/a)-a/2*ln(a^2+x^2)", "" },
	{ "asin(a*x)/acos(a*x)", "(2*a*x*asin(a*x)/acos(a*x)-ln(a^2*x^2+1))/(2*a)", "" },
	/* exp(a*x) */
	{ "exp(a*x)", "exp(a*x)/a", "" },
	{ "x*exp(a*x)", "exp(a*x)/a*(x-1/a)", "" },
	{ "x^m*exp(a*x)", "x^m*exp(a*x)/a-m/a*integral(x^(m-1)*exp(a*x),x)", "" },
	{ "exp(a*x)*sin(a*x)", "(exp(a*x)*(sin(a*x)-cos(a*x)))/(2*a)", "" },
	{ "exp(a*x)*sin(b*x)", "(exp(a*x)*(a*sin(b*x)-b*cos(b*x)))/(a^2+b^2)", "" },
	{ "cos(a*x)*exp(a*x)", "exp(a*x)*(cos(a*x)+sin(a*x))/(2*a)", "" },
	{ "cos(b*x)*exp(a*x)", "exp(a*x)*(a*cos(b*x)+b*sin(b*x))/(a^2+b^2)", "" },
	{ "cosh(a*x)*exp(a*x)", "exp(2*a*x)/(4*a)+x/2", "" },
	{ "cosh(b*x)*exp(a*x)", "exp(a*x)/(a^2-b^2)*(a*cosh(b*x)-b*sinh(b*x))", "" },
	{ "exp(a*x)*sinh(a*x)", "exp(2*a*x)/(4*a)-x/2", "" },
	{ "exp(a*x)*sinh(b*x)", "exp(a*x)/(a^2-b^2)*(a*sinh(b*x)-b*cosh(b*x))", "" },
	/* ln(a*x) */
	{ "ln(a*x)", "x*ln(a*x)-x", "" },
	{ "ln(a*x^m)", "x*ln(a*x^m)-m*x", "" },
	{ "x*ln(a*x)", "x^2/2*(ln(a*x)-1/2)", "" },
	{ "x^m*ln(a*x)", "x^(m+1)/(m+1)*(ln(a*x)-1/(m+1))", "" },
	{ "ln(a*x)/x", "ln(a*x)^2/2", "" },
	{ "ln(a*x)/(x^m)", "~ln(a*x)/((m-1)*x^(m-1))-1/((m-1)^2*x^(m-1))", "" },
	{ "ln(a*x)^n/x", "ln(a*x)^(n+1)/(n+1)", "" },
	{ "ln(a*x)^m/(x^n)", "~ln(a*x)^m/((n-1)*x^(n-1))+p/(n-1)*integral(ln(a*x)^(m-1)/(x^n),x)", "" },
	{ "1/(x*ln(a*x))", "ln(ln(a*x))", "" },
	{ "ln(a*x)^n", "x*ln(a*x)^n-n*integral(ln(a*x)^(n-1),x)", "" },
	{ "x*ln(a*x)^n", "(x^2*ln(a*x)^n)/2-n/2*integral(x*ln(a*x)^(n-1),x)", "" },
	{ "x^m*ln(a*x)^n", "(x^(m+1)*ln(a*x)^n)/(m+1)-n/(m+1)*integral(x^m*ln(a*x)^(n-1),x)", "" },
	{ "ln(a*x+b)", "(x+b/a)*ln(a*x+b)-x", "" },
	{ "x*ln(a*x+b)", "(b*x)/(2*a)-x^2/4+1/2*(x^2-b^2/a^2)*ln(a*x+b)", "" },
	{ "ln(c+a*x^2)", "(sqrt(a)*x*ln(~(a*x^2-c))-sqrt(c)*ln((sqrt(a)*x-sqrt(c))/(sqrt(a)*x+sqrt(c)))-2*sqrt(a)*x)/sqrt(a)", "a<0" },
	{ "ln(c+a*x^2)", "(sqrt(a)*x*ln(a*x^2+c)+2*(sqrt(c)*atan(sqrt(a)*x/(sqrt(c)))-sqrt(a)*x))/sqrt(a)", "" },
	{ "ln(a*x^2+b*x+c)", "1/a*sqrt(4*a*c-b^2)*atan((2*a*x)/sqrt(4*a*c-b^2))-2*x+(b/(2*a)+x)*ln(a*x^2+b*x+c)", "" },
	{ "sin(ln(a*x))", "x/2*(sin(ln(a*x))-cos(ln(a*x)))", "" },
	{ "cos(ln(a*x))", "x/2*(sin(ln(a*x))+cos(ln(a*x)))", "" },
	/* sinh(a*x) */
	{ "sinh(a*x)", "cosh(a*x)/a", "" },
	{ "x*sinh(a*x)", "x*cosh(a*x)/a-sinh(a*x)/a^2", "" },
	{ "1/sinh(a*x)", "ln(sinh(a*x)/(1+cosh(a*x)))/a", "" },
	{ "x^m*sinh(a*x)", "(x^m*cosh(a*x))/a-m/a*integral(x^(m-1)*cosh(a*x),x)", "" },
	{ "sinh(a*x)^n", "(sinh(a*x)^(n-1)*cosh(a*x))/(a*n)-(n-1)/n*integral(sinh(a*x)^(n-2),x)", "" },
	{ "1/(sinh(a*x)^n)", "~cosh(a*x)/(a*(n-1)*sinh(a*x)^(n-1))-(n-2)/(n-1)*integral(1/(sinh(a*x)^(n-2)),x)", "" },
	/* cosh(a*x) */
	{ "cosh(a*x)", "sinh(a*x)/a", "" },
	{ "x*cosh(a*x)", "x*sinh(a*x)/a-cosh(a*x)/a^2", "" },
	{ "1/cosh(a*x)", "2/a*atan(exp(a*x))", "" },
	{ "cosh(a*x)*cosh(b*x)", "sinh((a-b)*x)/(2*(a-b))+sinh((a+b)*x)/(2*(a+b))", "" },
	{ "x^m*cosh(a*x)", "(x^m*sinh(a*x))/a-m/a*integral(x^(m-1)*sinh(a*x),x)", "" },
	{ "cosh(a*x)^n", "cosh(a*x)^(n-1)*sinh(a*x)/(a*n)+(n-1)/n*integral(cosh(a*x)^(n-2),x)", "" },
	{ "1/(cosh(a*x)^n)", "sinh(a*x)/(a*(n-1)*cosh(a*x)^(n-1))+(n-2)/(n-1)*integral(1/cosh(a*x)^(n-2),x)", "" },
	/* sinh(a*x) && cosh(a*x)  */
	{ "cosh(a*x)*sinh(a*x)", "sinh(a*x)^2/(2*a)", "" },
	{ "cosh(a*x)*sinh(b*x)", "cosh((b+a)*x)/(2*(b+a))+(cosh((b-a)*x))/(2*(b-a))", "" },
	{ "cosh(a*x)*sinh(a*x)^n", "sinh(a*x)^(n+1)/((n+1)*a)", "" },
	{ "cosh(a*x)^n*sinh(a*x)", "cosh(a*x)^(n+1)/((n+1)*a)", "" },
	/* tanh(a*x) */
	{ "sinh(a*x)/cosh(a*x)", "ln(cosh(a*x))/a", "" },
	{ "sinh(a*x)^2/(cosh(a*x)^2)", "x-sinh(a*x)/(a*cos(a*x))", "" },
	/* coth(a*x) */
	{ "cosh(a*x)/sinh(a*x)", "ln(sinh(a*x))/a", "" },
	{ "cosh(a*x)^2/(sinh(a*x)^2)", "x-cosh(a*x)/(a*sinh(a*x))", "" },
	/* sech(a*x) = 1/cosh */
	{ "sinh(a*x)/(cosh(a*x)^n)", "~1/((n*a)*cosh(a*x)^n)", "" },
	{ "x/(cosh(a*x)^2)", "(x*sinh(a*x))/(a*cosh(a*x))-ln(cosh(a*x))/a^2", "" },
	/* csch(a*x) = 1/sinh */
	{ "cosh(a*x)/(sinh(a*x)^n)", "~1/(n*a*sinh(a*x)^n)", "" },
	{ "x/(sinh(a*x)^2)", "~x*cosh(a*x)/(a*sinh(a*x))+ln(sinh(a*x))/a^2", "" },
	/* inverse trigo hyperbolique */
	{ "asinh(x/a)", "x*asinh(x/a)-sqrt(a^2+x^2)", "" },
	{ "asinh(a*x)", "x*asinh(a*x)-sqrt(1+a^2*x^2)/a", "" },
	{ "acosh(x/a)", "x*acosh(x/a)-a*sqrt((~1+x/a)*(1+x/a))", "" },
	{ "acosh(a*x)", "x*acosh(a*x)-sqrt((~1+a*x)*(1+a*x))/a", "" },
	/* trigonometrique & hyperbolique */
	{ "cos(a*x)*cosh(b*x)", "(a*sin(a*x)*cosh(b*x)+b*cos(a*x)*sinh(b*x))/(a^2+b^2)", "" },
	{ "cos(a*x)*sinh(b*x)", "(a*sin(a*x)*sinh(b*x)+b*cos(a*x)*cosh(b*x))/(a^2+b^2)", "" },
	{ "sin(a*x)*sinh(b*x)", "(b*sin(a*x)*sinh(b*x)-b*cos(a*x)*cosh(b*x))/(a^2+b^2)", "" },
	{ "sin(a*x)*sinh(b*x)", "(b*sin(a*x)*cosh(b*x)-a*cos(a*x)*sinh(b*x))/(a^2+b^2)", "" }
};
