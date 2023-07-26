#include "integral.h"

int alg[2] = { 0, 0 }; // degré, membres
int ipp_loop = 10;

static map separate_factor(Tree* u, const char* x)
{
	if (!found_element(u, x))
		return push_back(push_back_map(NULL, u), new_tree("1"));
	if (u->tok_type == DIVID || u->tok_type == PROD)
	{
		map f = separate_factor(u->tleft, x), g = separate_factor(u->tright, x);
		Tree* free_of_part = join(clone(f->begin->data), clone(g->begin->data), fnc[u->tok_type].ex);
		Tree* dependent_part = join(clone(f->end->data), clone(g->end->data), fnc[u->tok_type].ex);
		f = clear_map(f); g = clear_map(g);
		return push_back(push_back(NULL, free_of_part), dependent_part);
	}
	return push_back_map(push_back(NULL, new_tree("1")), u);
}

map polycoeffs(Tree* u, const char* x)
{
	int i = 1;
	map cf = NULL;
	Tree* z = new_tree("0");
	Tree* r = simplify(remplace_tree(u, x, z)), * d = diff(u, x);
	cf = push_back(cf, r);
	while (strcmp(d->value, "0"))
	{
		r = simplify(join(remplace_tree(d, x, z), new_tree(tostr(factoriel(i))), fnc[DIVID].ex));
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
		if (!strcmp(element->from, s_form))
			return to_tree(In2post2(element->to));
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

static Tree* integral_try_factor(Tree* u, const char* x)
{
	if (is_symbolic(u))
		return clone(u);
	if (u->tok_type == ADD && ispoly(u, x))
	{
		map coefs = polycoeffs(u, x);
		if (coefs->length > 2)
		{
			if (ismonomial(u->tleft, x) && ismonomial(u->tright, x) && strcmp(((Tree*)coefs->end->data)->value, "0"))
			{
				Tree* a = degree_sv(u->tleft, x), * b = degree_sv(u->tright, x), * cf = NULL;
				Tree* c = simplify(join(new_tree(x), clone(a), fnc[POW].ex));
				mapCell* coef = coefs->begin->next;
				while (coef != NULL)
				{
					if (strcmp(((Tree*)coef->data)->value, "0"))
					{
						cf = coef->data;
						break;
					}
					coef = coef->next;
				}
				if (cf != NULL)
				{
					Tree* p = simplify(join(new_tree(x), join(b, a, fnc[SUB].ex), fnc[POW].ex));
					Tree* d = join(clone(cf), join(clone(coefs->begin->data), p, fnc[PROD].ex), fnc[ADD].ex);
					coefs = clear_map(coefs);
					return join(c, d, fnc[PROD].ex);
				}
				clean_tree(a); clean_tree(b); clean_tree(c);
			}
			if (coefs->length == 3)
			{
				coefs = clear_map(coefs);
				return square_free_factor(u, x);
			}
		}
		coefs = clear_map(coefs);
	}
	if (u->gtype == OPERAT)
		return join(integral_try_factor(u->tleft, x), integral_try_factor(u->tright, x), u->value);
	if (u->gtype == NEGATION || u->gtype == FUNCTION)
		return join(integral_try_factor(u->tleft, x), NULL, u->value);
	return clone(u);
}

static map trial_substitutions(Tree* f, map L)
{
	if (f->tok_type == POW || f->gtype == FUNCTION)
		L = push_back_map(L, f);
	else if (f->gtype == OPERAT)
	{
		L = trial_substitutions(f->tleft, L);
		L = trial_substitutions(f->tright, L);
	}
	else if (f->tok_type == NEGATIF)
		L = trial_substitutions(f->tleft, L);
	return L;
}

static Tree* Match_substitute(Tree* u, map Li)
{
	if (Li == NULL)
		return u;
	mapCell* tmp = Li->begin;
	while (tmp != NULL)
	{
		u = remplace_var(u, ((Tree*)tmp->data)->tleft->value, ((Tree*)tmp->data)->tright);
		tmp = tmp->next;
	}
	return u;
}

static bool match_var(Tree* Node, Tree* toMatch, map* w)
{
	if ((*w) != NULL)
	{
		mapCell* tmp = (*w)->begin;
		while (tmp != NULL)
		{
			if (tree_compare(((Tree*)tmp->data)->tleft, toMatch))
				return tree_compare(((Tree*)tmp->data)->tright, Node);
			tmp = tmp->next;
		}
	}
	*w = push_back(*w, join(clone(toMatch), clone(Node), fnc[EGAL].ex));
	return true;
}

static bool isMatchNode(Tree* Node, Tree* toMatch, const char* x, map* w)
{
	if (!strcmp(x, Node->value) && !strcmp(toMatch->value, "X"))
		return true;
	if (is_symbolic(Node) && toMatch->gtype == VAR && strlen(toMatch->value) > 0 && strstr("ABCDMNPQR", toMatch->value))
		return match_var(Node, toMatch, w);
	Tree* v = toMatch->tleft;
	token tk = toMatch->tok_type;
	if (tk == ADD && v->gtype == VAR && is_symbolic(Node) && is_symbolic(toMatch->tright) && strlen(v->value) > 0 && strstr("ABCDMNPQR", v->value))
	{
		Tree* c = simplify(join(join(clone(Node), clone(toMatch->tright), fnc[SUB].ex), new_tree("2"), fnc[DIVID].ex));
		if (is_int(c))
		{
			bool a = match_var(c, v, w);
			clean_tree(c);
			return a;
		}
		clean_tree(c);
		return false;
	}
	if ((tk == PROD || tk == ADD) && isMatchNode(Node, toMatch->tright, x, w) && v->gtype == VAR && strlen(v->value) > 0 && strstr("ABCDMNPQR", v->value))
	{
		Tree* c = new_tree((tk == PROD) ? "1" : "0");
		bool a = match_var(c, v, w);
		clean_tree(c);
		return a;
	}
	if (Node->gtype == toMatch->gtype)
		return !strcmp(Node->value, toMatch->value);
	return false;
}

static bool toMatchExpression(Tree* e, Tree* id, const char* x, map* w)
{
	if (!isMatchNode(e, id, x, w))
		return false;
	if (id->gtype == VAR)
		return true;
	if (e->gtype > VAR)
	{
		bool t = toMatchExpression(e->tleft, id->tleft, x, w);
		if (e->gtype >= OPERAT)
			t = t && toMatchExpression(e->tright, id->tright, x, w);
		return t;
	}
	return true;
}

static bool search_match(const char* ex, List* oper)
{
	if ((*oper) == NULL)
		return true;
	Cell* tmp = (*oper)->begin;
	while (tmp != NULL)
	{
		if (!strstr(ex, (char*)tmp->data))
			return false;
		tmp = tmp->next;
	}
	return true;
}

static Tree* match(Tree* u, struct Integral* ID, List* oper, const char* x, int IDSize)
{
	for (const Integral* element = ID; element != ID + IDSize; element++)
	{
		bool is_match = search_match(element->from, oper);
		if (is_match)
		{
			Tree* id_tr = to_tree(In2post2(element->from));
			map Li = NULL;
			is_match = toMatchExpression(u, id_tr, x, &Li);
			clean_tree(id_tr);
			if (is_match)
			{
				if (strlen(element->condition) > 0)
				{
					Tree* condt = to_tree(In2post2(element->condition));
					condt = Match_substitute(condt, Li);
					if (isconstant(condt->tleft))
					{
						double a = Eval(condt->tleft), b = Eval(condt->tright);
						bool t = false;
						if (condt->tok_type == SUPERIEUR)
							t = a > b;
						if (condt->tok_type == INFERIEUR)
							t = a < b;
						if (condt->tok_type == EGAL)
							t = a == b;
						clean_tree(condt);
						if (!t)
						{
							Li = clear_map(Li);
							continue;
						}
					}
				}
				Tree* form = to_tree(In2post2(element->to));
				form = Match_substitute(form, Li);
				Li = clear_map(Li);
				*oper = clear_dlist(*oper);
				return form;
			}
			Li = clear_map(Li);
		}
	}
	*oper = clear_dlist(*oper);
	return NULL;
}

static List getfunction(Tree* tr, const char* x, List list, List* oper)
{
	if (is_symbolic(tr))
		return list;
	if (tr->gtype == FUNCTION)
	{
		*oper = push_back_dlist(*oper, tr->value);
		if (list == NULL)
		{
			list = push_back_dlist(list, tr->value);
			if (tr->tok_type == SQRT_F)
				list = getfunction(tr->tleft, x, list, oper);
			return list;
		}
		Cell* tmp = list->begin;
		while (tmp != NULL)
		{
			if (!strcmp((char*)tmp->data, tr->value))
				return list;
			tmp = tmp->next;
		}
		list = push_back_dlist(list, tr->value);
		if (tr->tok_type == SQRT_F)
			list = getfunction(tr->tleft, x, list, oper);
		return list;
	}
	if (tr->tleft != NULL)
	{
		*oper = push_back_dlist(*oper, tr->value);
		list = getfunction(tr->tleft, x, list, oper);
		if (tr->tok_type == POW && tr->tright->tok_type == DIVID && !strcmp(tr->tright->tright->value, "2"))
			list = push_back_dlist(list, fnc[SQRT_F].ex);
		if (tr->tright != NULL)
			list = getfunction(tr->tright, x, list, oper);
		if (tr->tok_type == ADD && ispoly(tr, x))
		{
			map cf = polycoeffs(tr, x);
			int k = cf->length;
			string v = ((Tree*)cf->begin->next->data)->value;
			if (k > 2 && (!strcmp(v, "0") || (k == 3 && strcmp(v, "0"))))
			{
				mapCell* coef = cf->begin;
				while (coef != NULL)
				{
					if (!strcmp(((Tree*)coef->data)->value, "0"))
						k--;
					coef = coef->next;
				}
				alg[0] = max(alg[0], cf->length - 1);
				alg[1] = max(alg[1], k);
			}
			cf = clear_map(cf);
		}
	}
	return list;
}

static Tree* to_match(Tree* u, const char* x)
{
	FunctionFlags flags = { false }; // Initialisez tous les indicateurs à false
	List list_fnc = NULL, op = NULL;
	list_fnc = getfunction(u, x, list_fnc, &op);
	if (!list_fnc)
	{
		if (alg[0] == 2 && alg[1] == 3)
			return match(u, Integralalgx22, &op, x, AMOUNT_INTEGRAL_ALGX22);
		if (alg[0] == 2 && alg[1] == 2)
			return match(u, Integralalgx2, &op, x, AMOUNT_INTEGRAL_ALGX2);
		if (alg[0] == 3 && alg[1] == 2)
			return match(u, Integralalgx3, &op, x, AMOUNT_INTEGRAL_ALGX3);
		if (alg[0] == 4 && alg[1] == 2)
			return match(u, Integralalgx4, &op, x, AMOUNT_INTEGRAL_ALGX4);
		if (alg[1] == 2)
			return match(u, IntegralalgxN, &op, x, AMOUNT_INTEGRAL_ALGXN);
		return match(u, Integraltable, &op, x, AMOUNT_INTEGRAL);
	}
	Cell* tmp = list_fnc->begin;
	while (tmp != NULL)
	{
		token tk = tokens((char*)tmp->data, fnc);
		switch (tk) {
		case EXP_F:
			flags.i_exp = true;
			break;
		case LN_F:
			flags.i_ln = true;
			break;
		case SIN_F:
			flags.i_sin = true;
			break;
		case COS_F:
			flags.i_cos = true;
			break;
		case SQRT_F:
			flags.i_sqrt = true;
			break;
		case COSH_F:
			flags.i_cosh = true;
			break;
		case SINH_F:
			flags.i_sinh = true;
			break;
		case ASINH_F:
		case ACOSH_F:
			flags.i_itrigh = true;
			break;
		case ASIN_F:
		case ACOS_F:
			flags.i_itrig = true;
			break;
		default:
			break;
		}
		tmp = tmp->next;
	}
	list_fnc = clear_dlist(list_fnc);
	if (flags.i_exp)
		return match(u, Integralexp, &op, x, AMOUNT_INTEGRAL_EXP);
	if (flags.i_ln)
		return match(u, Integralln, &op, x, AMOUNT_INTEGRAL_LN);
	if (flags.i_itrigh)
		return match(u, Integralinvtrigh, &op, x, AMOUNT_INTEGRAL_INVTRIGH);
	if (flags.i_itrig)
		return match(u, Integralinvtrig, &op, x, AMOUNT_INTEGRAL_INVTRIG);
	if (flags.i_cosh && flags.i_sinh)
		return match(u, Integraltrigh, &op, x, AMOUNT_INTEGRAL_TRIGH);
	if (flags.i_cosh)
		return match(u, Integralcosh, &op, x, AMOUNT_INTEGRAL_COSH);
	if (flags.i_sinh)
		return match(u, Integralsinh, &op, x, AMOUNT_INTEGRAL_SINH);
	if (flags.i_cos && flags.i_sin)
		return match(u, Integraltrig, &op, x, AMOUNT_INTEGRAL_TRIG);
	if (flags.i_cos)
		return match(u, Integralcos, &op, x, AMOUNT_INTEGRAL_COS);
	if (flags.i_sin)
		return match(u, Integralsin, &op, x, AMOUNT_INTEGRAL_SIN);
	if (flags.i_sqrt)
	{
		if (alg[0] == 2 && alg[1] == 2)
			return match(u, Integralsqrt_X2, &op, x, AMOUNT_INTEGRAL_SQRTX2);
		if (alg[0] == 2 && alg[1] == 3)
			return match(u, Integralsqrt_X22, &op, x, AMOUNT_INTEGRAL_SQRTX22);
		return match(u, Integralsqrt, &op, x, AMOUNT_INTEGRAL_SQRT);
	}
	return NULL;
}

static Tree* integral_sub(Tree* u)
{
	if (u->tok_type == INTEGRAL_F)
	{
		u->tleft->tleft = pow_transform(simplify(u->tleft->tleft));
		return integral(u->tleft->tleft, u->tleft->tright->value);
	}
	if (u->tok_type == NEGATIF)
		return join(integral_sub(u->tleft), NULL, u->value);
	if (u->gtype == OPERAT)
		return join(integral_sub(u->tleft), integral_sub(u->tright), u->value);
	return clone(u);
}

static Tree* poly_integral(Tree* f, const char* x)
{
	map coefs = polycoeffs(f, x);
	int i = coefs->length;
	mapCell* coef = coefs->begin;
	while (coef != NULL)
	{
		if (strcmp(((Tree*)coef->data)->value, "0"))
			coef->data = simplify(join(coef->data, new_tree(tostr(i)), fnc[DIVID].ex));
		i--;
		coef = coef->next;
	}
	coefs = push_back(coefs, new_tree("0"));
	return polyreconstitute(&coefs, x);
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
			clean_tree(s);
			clean_tree(t);
			return NULL;
		}
		return join(s, t, f->value);
	}
	return NULL;
}

static Tree* integral_table(Tree* f, const char* x)
{
	if (ispoly(f, x) && (f->tok_type != POW || (f->tok_type == POW && ismonomial(f->tleft, x))))
		return poly_integral(f, x);
	if (f->tok_type == ADD)
		return linear_priorities(f, x);
	map integ_sep = separate_factor(f, x);
	Tree* form = to_match(integ_sep->end->data, x);
	if (form != NULL)
	{
		Tree* w = join(clone(integ_sep->begin->data), integral_sub(form), fnc[PROD].ex);
		integ_sep = clear_map(integ_sep);
		clean_tree(form);
		if (strcmp(x, "X"))
		{
			Tree* v = new_tree(x);
			w = remplace_var(w, "X", v);
			clean_tree(v);
		}
		return w;
	}
	integ_sep = clear_map(integ_sep);
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
		if (!found_element(tmp->data, x))
		{
			Tree* u = join(clone(f), diff(tmp->data, x), fnc[DIVID].ex);
			Tree* s = simplify(substitute(u, tmp->data, v));
			if (!found_element(s, x) && strcmp(s->value, fnc[UNDEF].ex))
				F = remplace_tree(integral(s, v->value), v->value, tmp->data);
			clean_tree(u); clean_tree(s);
		}
		tmp = tmp->next;
	}
	P = clear_map(P);
	clean_tree(v);
	return F;
}

Tree* integral(Tree* f, const char* x)
{
	Tree* f_x = integral_try_factor(f, x);
	Tree* F = integral_table(f_x, x);
	if (!F)
		F = linear_priorities(f_x, x);
	if (!F)
		F = sustitution_method(f_x, x);
	if (!F)
	{
		Tree* g = algebraic_expand(clone(f_x));
		if (!tree_compare(f_x, g))
			F = integral(g, x);
		clean_tree(g);
	}
	clean_tree(f_x);
	return F;
}

struct Integral Integralsqrt[] =
{
	/* sqrt(B+A*X) */
	{ "sqrt(X)", "2/3*X^(3/2)", "" },
	{ "sqrt(A*X)", "2*X*sqrt(A*X)/3", "" },
	{ "1/sqrt(X)", "2*sqrt(X)", "" },
	{ "1/sqrt(A*X)", "2*sqrt(A*X)/A", "" },
	{ "1/sqrt(B+A*X)", "2*sqrt(B+A*X)/A", "" },
	{ "X/sqrt(B+A*X)", "2*(A*X-2*B)/(3*A^2)*sqrt(B+A*X)", "" },
	{ "1/(X*sqrt(B+A*X))", "ln((sqrt(B+A*X)-sqrt(B))/(sqrt(B+A*X)+sqrt(B)))/sqrt(B)", "" },
	{ "1/(X^2*sqrt(B+A*X))", "~sqrt(B+A*X)/(B*X)-A/(2*B)*integral(1/(X*sqrt(B+A*X)),X)", "" },
	{ "sqrt(B+A*X)", "2*sqrt((B+A*X)^3)/(3*A)", "" },
	{ "X*sqrt(B+A*X)", "2*(3*A*X-2*B)/(15*A^2)*sqrt((B+A*X)^3)", "" },
	{ "sqrt(B+A*X)/X", "2*sqrt(B+A*X)+B*integral(1/(X*sqrt(B+A*X)),X)", "" },
	{ "sqrt(B+A*X)/X^2", "~sqrt(B+A*X)/A+X/2*integral(1/(X*sqrt(B+A*X)),X)", "" },
	{ "X^N/sqrt(B+A*X)", "2*X^N*sqrt(B+A*X)/((2*N+1)*A)-2*N*B/((2*N+1)*A)*integral(X^(N-1)/sqrt(B+A*X),X)", "" },
	{ "1/(X^N*sqrt(B+A*X))", "~sqrt(B+A*X)/((N-1)*B*X^(N-1))-(2*N-3)*A/((2*N-2)*B)*integral(1/(X^(N-1)*sqrt(B+A*X)),X)", "" },
	{ "X^N*sqrt(B+A*X)", "2*X^N/((2*N+3)*A)*(B+A*X)^(3/2)-2*N*B/((2*N+3)*A)*integral(X^(N-1)*sqrt(B+A*X),X)", "" },
	{ "sqrt(B+A*X)/(X^N)", "~sqrt(B+A*X)/((N-1)*X^(N-1))+A/(2*(N-1))*integral(1/(X^(N-1)*sqrt(B+A*X)),X)", "" },
	{ "(B+A*X)^(N/2)", "2*(B+A*X)^((N+2)/2)/(A*(N+2))", "" },
	{ "X*(B+A*X)^(N/2)", "2*(B+A*X)^((N+4)/2)/(A^2*(N+4))-2*B*(B+A*X)^((N+2)/2)/(A^2*(N+2))", "" },
	{ "X^2*(B+A*X)^(N/2)", "2*(B+A*X)^((N+6)/2)/(A^3*(N+6))-4*B*(B+A*X)^((N+4)/2)/(A^3*(N+4))+2*B^2*(B+A*X)^((N+2)/2)/(A^3*(N+2))", "" },
	{ "(B+A*X)^(N/2)/X", "2*(B+A*X)^(N/2)/N+B*integral((B+A*X)^((N-2)/2)/X,X)", "" },
	{ "(B+A*X)^(N/2)/X^2", "~(B+A*X)^((N+2)/2)/(B*X)+(N*A)/(2*B)*integral((B+A*X)^(N/2)/X,X)", "" },
	{ "1/(X*(B+A*X)^(N/2))", "2/((N-2)*B*(B+A*X)^((N-2)/2))+1/B*integral(1/(X*(B+A*X)^((N-2)/2)),X)", "" },
	/* sqrt(B+A*X) & P*X+Q */
	{ "(Q+P*X)/sqrt(B+A*X)", "(2*(A*P*X+3*A*Q-2*B*P))/(3*A^2)*sqrt(B+A*X)", "" },
	{ "1/((Q+P*X)*sqrt(B+A*X))", "ln((sqrt(P*(B+A*X))-sqrt(B*P-A*Q))/(sqrt(P*(B+A*X))+sqrt(B*P-A*Q)))/(sqrt(B*P-A*Q)*sqrt(P))", "" },
	{ "sqrt(B+A*X)/(Q+P*X)", "2*sqrt(B+A*X)/P+sqrt(B*P-A*Q)/(P*sqrt(Q))*ln((sqrt(P*(B+A*X))-sqrt(B*P-A*Q))/(sqrt(P*(B+A*X))+sqrt(B*P-A*Q)))", "" },
	{ "(Q+P*X)^N*sqrt(B+A*X)", "2*(Q+P*X)^(N+1)*sqrt(B+A*X)/((2*N+3)*P)+(B*P-A*Q)/((2*N+3)*P)*integral((Q+P*X)^N/sqrt(B+A*X),X)", "" },
	{ "1/((Q+P*X)^N*sqrt(B+A*X))", "sqrt(B+A*X)/((N-1)*(A*Q-B*P)*(Q+P*X)^(N-1))+(2*N-3)*A/(2*(N-1)*(A*Q-B*P))*integral(1/((Q+P*X)^(N-1)*sqrt(B+A*X)),X)", "" },
	{ "(Q+P*X)^N/sqrt(B+A*X)", "2*(Q+P*X)^N*sqrt(B+A*X)/((2*N+1)*A)+2*N*(A*Q-B*P)/((2*N+1)*A)*integral((Q+P*X)^(N-1)/sqrt(B+A*X),X)", "" },
	{ "sqrt(B+A*X)/(Q+P*X)^N", "~sqrt(B+A*X)/((N-1)*P*(Q+P*X)^(N-1))+A/(2*(N-1)*P)*integral(1/((Q+P*X)^(N-1)*sqrt(B+A*X)),X)", "" },
	/* sqrt(B+A*X) & sqrt(Q+P*X) */
	{ "1/sqrt((B+A*X)*(Q+P*X))", "2/sqrt(A*P)*ln(sqrt(A*(Q+P*X))+sqrt(P*(B+A*X)))", "" },
	{ "X/sqrt((B+A*X)*(Q+P*X))", "sqrt((B+A*X)*(Q+P*X))/(A*P)-(B*P+A*Q)/(2*A*P)*integral(1/sqrt((B+A*X)*(Q+P*X)),X)", "" },
	{ "sqrt((B+A*X)*(Q+P*X))", "(2*A*P*X+B*P+A*Q)/(4*A*P)*sqrt((B+A*X)*(Q+P*X))-(B*P-A*Q)^2/(8*A*P)*integral(1/sqrt((B+A*X)*(Q+P*X)),X)", "" },
	{ "sqrt(Q+P*X)/sqrt(B+A*X)", "sqrt((B+A*X)*(Q+P*X))/A+(A*Q-B*P)/(2*A)*integral(1/sqrt((B+A*X)*(Q+P*X)),X)", "" },
	{ "1/((Q+P*X)*sqrt((B+A*X)*(Q+P*X)))", "2*sqrt(B+A*X)/((A*Q-B*P)*sqrt(Q+P*X))", "" }
};

struct Integral Integralsqrt_X2[] =
{
	/* sqrt(C+A*X^2) */
	{ "sqrt(A+X^2)", "1/2*(X*sqrt(A+X^2)+A*ln(X+sqrt(A+X^2)))", "" },
	{ "sqrt(A-X^2)", "1/2*(X*sqrt(A-X^2)+A*asin(X/sqrt(A)))", "" },
	{ "1/sqrt(A+X^2)", "ln(X+sqrt(A+X^2))", "" },
	{ "1/sqrt(A-X^2)", "asin(X/sqrt(A))", "" },
	{ "sqrt(C+~A*X^2)", "X/2*sqrt(C-A*X^2)+C/(2*sqrt(A))*asin(X*sqrt(A/C))", "" },
	{ "sqrt(C+A*X^2)", "X/2*sqrt(C+A*X^2)+C/(2*sqrt(A))*ln(X*sqrt(A)+sqrt(C+A*X^2))", "" },
	{ "1/sqrt(C+~A*X^2)", "asin(X*sqrt(A/C))/sqrt(A)", "" },
	{ "1/sqrt(C+A*X^2)", "ln(X*sqrt(A)+sqrt(C+A*X^2))/sqrt(A)", "" },
	{ "X*sqrt(C+A*X^2)", "(C+A*X^2)^(3/2)/(3*A)", "" },
	{ "X^2*sqrt(C+~A*X^2)", "X/(4*A)*(C-A*X^2)^(3/2)-C*X/(8*A)*sqrt(C-A*X^2)-C^2/(8*A^(3/2))*ln(C+X*sqrt(A)+sqrt(A*X^2))", "" },
	{ "X^2*sqrt(C+A*X^2)", "~(C^2*ln(sqrt(A*X^2+C)+sqrt(A)*X)-sqrt(A)*X*sqrt(A*X^2+C)*(2*A*X^2+C))/(8*A^(3/2))", "" },
	{ "X/sqrt(C+A*X^2)", "sqrt(C+A*X^2)/A", "" },
	{ "X^2/sqrt(C+A*X^2)", "X*sqrt(C+A*X^2)/A-1/A*integral(sqrt(C+A*X^2),X)", "" },
	{ "sqrt(~C+A*X^2)/X", "sqrt(~C+A*X^2)-sqrt(C)*atan(sqrt(~C+A*X^2)/sqrt(C))", "" },
	{ "sqrt(C+A*X^2)/X", "sqrt(C+A*X^2)+sqrt(C)*ln((sqrt(C+A*X^2)-sqrt(C))/X)", "" },
	{ "1/(X*sqrt(C+~1*X^2))", "~ln((sqrt(C)+sqrt(C-X^2))/X)/sqrt(C)", "" },
	{ "1/(X*sqrt(C+X^2))", "~ln((sqrt(C)+sqrt(C-X^2))/X)/sqrt(C)", "" },
	{ "1/(X*sqrt(~C+X^2))", "acos(sqrt(C)/X)/sqrt(C)", "" },
	{ "1/(X*sqrt(~C+A*X^2))", "1/(sqrt(C)*cos(X*sqrt(A/C)))", "" },
	{ "1/(X*sqrt(C+A*X^2))", "ln((sqrt(C+A*X^2)-sqrt(C))/X)/sqrt(C)", "" },
	{ "1/(X^2*sqrt(C+A*X^2))", "~sqrt(C+A*X^2)/(C*X)", "" },
	{ "X^N/sqrt(C+A*X^2)", "X^(N-1)*sqrt(C+A*X^2)/(N*A)-(N-1)*C/(N*A)*integral(X^(N-2)/sqrt(C+A*X^2),X)", "" },
	{ "X^N*sqrt(C+A*X^2)", "X^(N-1)*(C+A*X^2)^(3/2)/((N+2)*A)-(N-1)*C/((N+2)*A)*integral(X^(N-2)*sqrt(C+A*X^2),X)", "" },
	{ "sqrt(C+A*X^2)/X^N", "~(C+A*X^2)^(3/2)/(C*(N-1)*X^(N-1))-(N-4)*A/((N-1)*C)*integral(sqrt(C+A*X^2)/X^(N-2),X)", "" },
	{ "1/(X^N*sqrt(C+A*X^2))", "~sqrt(C+A*X^2)/(C*(N-1)*X^(N-1))-(N-2)*A/((N-1)*C)*integral(1/(X^(N-2)*sqrt(C+A*X^2)),X)", "" },
	{ "(C+~A*X^2)^(3/2)", "X/8*(5*C-2*A*X^2)*sqrt(C-A*X^2)+3*C^2/(8*sqrt(A))*asin(X*sqrt(A/C))", "" },
	{ "(C+A*X^2)^(3/2)", "X/8*(5*C+2*A*X^2)*sqrt(C+A*X^2)+3*C^2/(8*sqrt(A))*ln(X*sqrt(A)+sqrt(C+A*X^2))", "" },
	{ "1/(C+A*X^2)^(3/2)", "X/(C*sqrt(C+A*X^2))", "" },
	{ "X*sqrt(C+A*X^2)", "(C+A*X^2)^(3/2)/(3*A)", "" },
	{ "X^N*sqrt(C+A*X^2)", "X^(N+1)*(C+A*X^2)^(3/2)/(N+2)+3*C/(N+4)*integral(X^N*sqrt(C+A*X^2),X)", "" },
	{ "X/(C+A*X^2)^(3/2)", "~1/(A*sqrt(C+A*X^2))", "" },
	{ "X^2/(C+~A*X^2)^(3/2)", "~X/(A*sqrt(C-A*X^2))+asin(X*sqrt(A/C))/(A*sqrt(A))", "" },
	{ "X^2/(C+A*X^2)^(3/2)", "~X/(A*sqrt(C+A*X^2))+ln(X*sqrt(A)+sqrt(C+A*X^2))/(A*sqrt(A))", "" },
	{ "X^3/(C+A*X^2)^(3/2)", "~X^2/(A*sqrt(C+A*X^2))+2/A^2*sqrt(C+A*X^2)", "" },
	{ "1/(X*(C+A*X^N))", "ln(X^N/(C+A*X^N))/(C*N)", "" },
	{ "1/(X*sqrt(~C+A*X^N))", "1/(N*sqrt(C)*acos(sqrt(A*X^N/C)))", "" },
	{ "1/(X*sqrt(C+A*X^N))", "ln((sqrt(C+A*X^N)-sqrt(C))/(sqrt(C+A*X^N)+sqrt(C)))/(N*sqrt(C))", "" },
	{ "X^M*(C+A*X^N)^P", "1/(M-1+N*P)*(X^(M-1)*(C+A*X^N)^P+N*P*C*integral(X^M(C+A*X^N)^(P-1),X))", "" },
	{ "X^M/(C+A*X^N)^P", "(integral(X^(M-N)/(C+A*X^N)^(P-1),X)-C*integral(X^(M-N)/(C+A*X^N)^P,X))/A", "" },
	{ "1/(X^M*(C+A*X^N)^P)", "(integral(1/(X^M*(C+A*X^N)^(P-1)),X)-A*integral(1/(X^(M-N)*(C+A*X^N)^P),X))/C", "" }
};

struct Integral Integralsqrt_X22[] =
{
	/* sqrt(C+B*X+A*X^2) */
	{ "sqrt(C+B*X+A*X^2)", "((2*A*X+B)*sqrt(C+B*X+A*X^2))/(4*A)+(4*A*C-B^2)/(8*A)*integral(1/sqrt(C+B*X+A*X^2),X)", "" },
	{ "X*sqrt(C+B*X+A*X^2)", "(C+B*X+A*X^2)^(3/2)/(3*A)-(B*(2*A*X+B))/(8*A^2)*sqrt(C+B*X+A*X^2)-(B*(4*A*C-B^2))/(16*A^2)*integral(1/sqrt(C+B*X+A*X^2),X)", "" },
	{ "X^2*sqrt(C+B*X+A*X^2)", "(6*A*X-5*B)/(24*A^2)*(C+B*X+A*X^2)^(3/2)+(5*B^2-4*A*C)/(16*A^2)*integral(sqrt(C+B*X+A*X^2),X)", "" },
	{ "1/sqrt(C+B*X+A*X^2)", "ln(2*sqrt(A)*sqrt(C+B*X+A*X^2)+2*A*X+B)/sqrt(A)", "" },
	{ "X/sqrt(C+B*X+A*X^2)", "sqrt(C+B*X+A*X^2)/A-B/(2*A)*integral(1/sqrt(C+B*X+A*X^2),X)", "" },
	{ "X^2/sqrt(C+B*X+A*X^2)", "(2*A*X-3*B)/(4*A^2)*sqrt(C+B*X+A*X^2)+(3*B^2-4*A*C)/(8*A^2)*integral(1/sqrt(C+B*X+A*X^2),X)", "" },
	{ "1/(X*sqrt(C+B*X+A*X^2))", "~1/sqrt(C)*ln((2*sqrt(C)*sqrt(C+B*X+A*X^2)+B*X+2*C)/X)", "" },
	{ "1/(X^2*sqrt(C+B*X+A*X^2))", "~sqrt(C+B*X+A*X^2)/(C*X)-B/(2*C)*integral(1/(X*sqrt(C+B*X+A*X^2)),X)", "" },
	{ "sqrt(C+B*X+A*X^2)/X", "sqrt(C+B*X+A*X^2)+B/2*integral(1/sqrt(C+B*X+A*X^2),X)+C*integral(1/(X*sqrt(C+B*X+A*X^2)),X)", "" },
	{ "sqrt(C+B*X+A*X^2)/X^2", "~sqrt(C+B*X+A*X^2)/A+X*integral(1/sqrt(C+B*X+A*X^2),X)+B/2*integral(1/(X*sqrt(C+B*X+A*X^2)),X)", "" },
	{ "1/(C+B*X+A*X^2)^(3/2)", "1/(2*A^(3/2)*(X-B/(2*A))^2)", "B^2=4*A*C" },
	{ "1/(C+B*X+A*X^2)^(3/2)", "2*(2*A*X+B)/((4*A*C-B^2)*sqrt(C+B*X+A*X^2))", "" },
	{ "X/(C+B*X+A*X^2)^(3/2)", "2*(B*X+2*C)/((B^2-4*A*C)*sqrt(C+B*X+A*X^2))", "" },
	{ "X^2/(C+B*X+A*X^2)^(3/2)", "((2*B^2-4*A*C)*X+2*B*C)/(A*(4*A*C-B^2)*sqrt(C+B*X+A*X^2))+1/A*integral(1/sqrt(C+B*X+A*X^2),X)", "" },
	{ "1/(X*(C+B*X+A*X^2)^(3/2))", "1/(C*sqrt(C+B*X+A*X^2))+1/C*integral(1/(X*sqrt(C+B*X+A*X^2)),X)-B/(2*C)*integral(1/(C+B*X+A*X^2)^(3/2),X)", "" },
	{ "1/(X^2*(C+B*X+A*X^2)^(3/2))", "~(A*X^2+2*B*X+C)/(C^2*X*sqrt(C+B*X+A*X^2))+(B^2-2*A*C)/(2*C^2)*integral(1/(C+B*X+A*X^2)^(3/2),X)-(3*B)/(2*C^2)*integral(1/(X*sqrt(C+B*X+A*X^2)),X)", "" },
	{ "(C+B*X+A*X^2)^(N+1/2)", "(2*A*X+B)*(C+B*X+A*X^2)^(N+1/2)/(4*A*(N+1))+(2*N+1)*(4*A*C-B^2)/(8*A*(N+1))*integral((C+B*X+A*X^2)^(N-1/2),X)", "" },
	{ "X*(C+B*X+A*X^2)^(N+1/2)", "(C+B*X+A*X^2)^(N+3/2)/(A*(2*N+3))-B/(2*A)*integral((C+B*X+A*X^2)^(N+1/2),X)", "" },
	{ "1/((C+B*X+A*X^2)^(N+1/2))", "2*(B+A*X)/((2*N-1)*(4*A*C-B^2)*(C+B*X+A*X^2)^(N-1/2))+8*A*(N-1)/((2*N-1)*(4*A*C-B^2))*integral(1/(C+B*X+A*X^2)^(N-1/2),X)", "" },
	{ "1/(X*(C+B*X+A*X^2)^(N+1/2))", "1/((2*N-1)*C*(C+B*X+A*X^2)^(N-1/2))+1/C*integral(1/(X*(C+B*X+A*X^2)^(N-1/2)),X)-B/(2*C)*integral(1/(C+B*X+A*X^2)^(N+1/2),X)", "" }
};

struct Integral Integralcos[] =
{
	/* cos(A*X) */
	{ "cos(A*X)", "sin(A*X)/A", "" },
	{ "cos(C*ln(B+A*X))", "1/(A*(C^2+1))*((A*X+B)*(C*sin(C*ln(A*X+B))+cos(C*ln(A*X+B))))", "" },
	{ "cos(A*X)^N", "sin(A*X)*cos(A*X)^(N-1)/(A*N)+(N-1)/N*integral(cos(A*X)^(N-2),X)", "" },
	{ "X*cos(A*X)", "cos(A*X)/A^2+(X*sin(A*X))/A", "" },
	{ "X*cos(A*X)^2", "X^2/4+X*sin(2*A*X)/(4*A)+cos(2*A*X)/(8*A^2)", "" },
	{ "X^M*cos(A*X)", "X^M*sin(A*X)/A+(M*X^(M-1))/A^2*cos(A*X)-M*(M-1)/A^2*integral(X^(M-2)*cos(A*X),X)", "" },
	{ "cos(A*X)*cos(B*X)", "sin((A-B)*X)/(2*(A-B))+sin((A+B)*X)/(2*(A+B))", "" },
	{ "1/cos(A*X)", "ln(tan(A*X)+1))/A", "" },
	{ "1/cos(A*X)^2", "tan(A*X)/A", "" },
	{ "X/cos(A*X)^2", "X*tan(A*X)/A+1/A^2*ln(cos(A*X))", "" },
	{ "1/cos(A*X)^N", "sin(A*X)/(A*(N-1)*cos(A*X)^(N-1))+(N-2)/(N-1)*integral(1/cos(A*X)^(N-2),X)", "" },
	{ "X/cos(A*X)^N", "X*sin(A*X)/(A*(N-1)*cos(A*X)^(N-1))-1/(A^2*(N-1)*(N-2)*cos(A*X)^(N-2))+(N-2)/(N-1)*integral(X/cos(A*X)^(N-2),X)", "" },
	{ "1/(1+~1*cos(A*X))", "~1/(A*tan(A*X/2))", "" },
	{ "X/(1+~1*cos(A*X))", "~X/(A*tan(A*X/2))+2/A^2*ln(sin(A*X/2))", "" },
	{ "1/(1+cos(A*X))", "tan(A*X/2)/A", "" },
	{ "X/(1+cos(A*X))", "X/A*tan(A*X/2)+2/A^2*ln(cos(A*X/2))", "" },
	{ "1/(1+~1*cos(A*X))^2", "~1/(2*A*tan(A*X/2))-1/(6*A*tan(A*X/2)^3)", "" },
	{ "1/(1+cos(A*X))^2", "tan(A*X/2)/(2*A)+tan(A*X/2)^3/(6*A)", "" },
	{ "1/(P+Q*cos(A*X))", "2/(A*sqrt(P^2-Q^2))*atan(sqrt((P-Q)/(P+Q)))*tan(A*X/2)", "" },
	{ "1/(P+Q*cos(A*X))^2", "Q*sin(A*X)/(A*(Q^2-P^2)*(P+Q*cos(A*X)))-P/(Q^2-P^2)*integral(1/(P+Q*cos(A*X)),X)", "" },
	{ "1/(P+Q*cos(A*X)^2", "1/(A*sqrt(P)*sqrt(P+Q))*atan(sqrt(P)*tan(A*X)/sqrt(P+Q))", "" },
	{ "cos(A*X)/(Q+P*cos(A*X))", "X/Q-P/Q*integral(1/(P+Q*cos(A*X)),X)", "" }
};

struct Integral Integralsin[] =
{
	/* sin(A*X) */
	{ "sin(A*X)", "~cos(A*X)/A", "" },
	{ "sin(C*ln(B+A*X))", "1/(A*(C^2+1))*((A*X+B)*(sin(C*ln(A*X+B))-C*cos(C*ln(A*X+B))))", "" },
	{ "sin(A*X)^N", "~sin(A*X)^(N-1)*cos(A*X)/(A*N)+(N-1)/N*integral(sin(A*X)^(N-2),X)", "" },
	{ "X*sin(A*X)", "sin(A*X)/A^2-X*cos(A*X)/A", "" },
	{ "X*sin(A*X)^2", "X^2/4-X*sin(2*A*X)/(4*A)-cos(2*A*X)/(8*A^2)", "" },
	{ "X^M*sin(A*X)", "~X^M*cos(A*X)/A+M*X^(M-1)*sin(A*X)/A^2-M*(M-1)/A^2*integral(X^(M-2)*sin(A*X),X)", "" },
	{ "sin(A*X)*sin(B*X)", "sin((A-B)*X)/(2*(A-B))-sin((A+B)*X)/(2*(A+B))", "" },
	{ "1/sin(A*X)", "ln(tan(A*X)+1))/A", "" },
	{ "1/sin(A*X)^2", "~1/(A*tan(A*X))", "" },
	{ "X/sin(A*X)^2", "~X/(A*tan(A*X))+1/A^2*ln(sin(A*X))", "" },
	{ "1/sin(A*X)^N", "~cos(A*X)/(A*(N-1)*sin(A*X)^(N-1))+(N-2)/(N-1)*integral(1/sin(A*X)^(N-2),X)", "" },
	{ "X/sin(A*X)^N", "~X*cos(A*X)/(A*(N-1)*sin(A*X)^(N-1))-1/(A^2*(N-1)*(N-2)*sin(A*X)^(N-2))+(N-2)/(N-1)*integral(X/sin(A*X)^(N-2),X)", "" },
	{ "sin(A*X)/(Q+P*sin(A*X))", "X/Q-P/Q*integral(1/(P+Q*sin(A*X)),X)", "" },
	{ "1/(1+~1*sin(A*X))", "tan(PI/4+A*X/2)/A", "" },
	{ "X/(1+~1*sin(A*X))", "X/A*tan(PI/4+A*X/2)+2/A^2*ln(sin(PI/4-A*X/2))", "" },
	{ "1/(1+sin(A*X))", "~tan(PI/4-A*X/2)/A", "" },
	{ "X/(1+sin(A*X))", "~X/A*tan(PI/4-A*X/2)+2/(A^2)*ln(sin(PI/4+A*X/2))", "" },
	{ "1/(1+~1*sin(A*X))^2", "tan(PI/4+A*X/2)/(2*A)+tan(PI/4+A*X/2)^3/(6*A)", "" },
	{ "1/(1+sin(A*X))^2", "~tan(PI/4-A*X/2)/(2*A)-tan(PI/4-A*X/2)^3/(6*A)", "" },
	{ "1/(P+Q*sin(A*X))", "2/(A*sqrt(P^2-Q^2))*atan((P*tan(1/2*A*X)+Q)/sqrt(P^2-Q^2))", "" },
	{ "1/(P+Q*sin(A*X))^2", "Q*cos(A*X)/(A*(P^2-Q^2)*(P+Q*sin(A*X)))+P/(P^2-Q^2)*integral(1/(P+Q*sin(A*X)),X)", "" },
	{ "1/(P+Q*sin(A*X)^2)", "1/(A*sqrt(P)*sqrt(P+Q))*atan((sqrt(P+Q)*tan(A*X))/sqrt(P))", "" }
};

struct Integral Integraltrig[] =
{
	/* cos(A*X) && sin(A*X) */
	{ "cos(A*X)*sin(A*X)", "sin(A*X)^2/(2*A)", "" },
	{ "cos(A*X)*sin(B*X)", "~cos((B-A)*X)/(2*(B-A))-cos((B+A)*X)/(2*(B+A))", "" },
	{ "cos(A*X)*sin(A*X)^N", "sin(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cos(A*X)^N*sin(A*X)", "~cos(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cos(A*X)^2*sin(A*X)^2", "X/8-sin(A*X)^4/(32*A)", "" },
	{ "cos(A*X)^M*sin(A*X)^N", "~sin(A*X)^(N-1)*cos(A*X)^(M+1)/(A*(N+M))+(N-1)/(N+M)*integral(cos(A*X)^M*sin(A*X)^(N-2),X)", "" },
	/* tan(A*X) */
	{ "sin(A*X)/cos(A*X)", "~1/A*ln(cos(A*X))", "" },
	{ "sin(A*X)/cos(A*X)^3", "1/(2*A*cos(A*X)^2)", "" },
	{ "sin(A*X)^N/cos(A*X)^M", "tan(A*X)^(N+1)/(N+1)", "M=N+2" },
	{ "X*sin(A*X)^2/cos(A*X)^2", "X*tan(A*X)/A+1/A^2*ln(cos(A*X))-X^2/2", "" },
	{ "sin(A*X)^N/cos(A*X)^N", "tan(A*X)^(N-1)/((N-1)*A)-integral(sin(A*X)^(N-2)/cos(A*X)^(N-2),X)", "" },
	/* cot(A*X) */
	{ "cos(A*X)/sin(A*X)", "ln(sin(A*X))/A", "" },
	{ "cos(A*X)^2/(1+~1*cos(A*X)^2)", "~1/(A*tan(A*X))-X", "" },
	{ "cos(A*X)/sin(A*X)^3", "~1/(2*A*sin(A*X)^2)", "" },
	{ "cos(A*X)^N/sin(A*X)^M", "~1/((N+1)*A*tan(A*X)^(N+1))", "M=N+2" },
	{ "X*cos(A*X)^2/(1+~1*cos(A*X)^2)", "~X/(A*tan(A*X))+1/A^2*ln(sin(A*X))-X^2/2", "" },
	{ "cos(A*X)^N/sin(A*X)^N", "~1/((N-1)*A*tan(A*X)^(N-1))-integral(cos(A*X)^(N-2)/sin(A*X)^(N-2),X)", "" },
	{ "sin(A*X)/cos(A*X)^N", "1/(N*A*cos(A*X)^N)", "" },
	{ "cos(A*X)/sin(A*X)^N", "~1/(N*A*sin(A*X)^N)", "" },
	/* fin cot */
	{ "1/(cos(A*X)*sin(A*X))", "ln(tan(A*X))/A", "" },
	{ "1/(cos(A*X)^2*sin(A*X)^2)", "(2*sin(A*X)^2-1)/(A*sin(A*X)*cos(A*X))", "" },
	{ "1/(cos(A*X)^2*sin(A*X))", "ln(sin(A*X)/(cos(A*X)+1))/A+1/acos(A*X)", "" },
	{ "sin(A*X)^2/cos(A*X)", "ln(~cos(A*X)/(sin(A*X)-1))/A-sin(A*X)/A", "" },
	{ "cos(A*X)^2/sin(A*X)", "cos(A*X)/A+1/A*ln(sin(A*X)/(cos(A*X)+1))", "" },
	{ "sin(A*X)^M/cos(A*X)^N", "sin(A*X)^(M-1)/(A*(N-1)*cos(A*X)^(N-1))-(M-1)/(N-1)*integral(sin(A*X)^(M-2)/cos(A*X)^(N-2),X)", "" },
	{ "cos(A*X)^M/sin(A*X)^N", "~cos(A*X)^(M-1)/(A*(N-1)*sin(A*X)^(N-1))-(M-1)/(N-1)*integral(cos(A*X)^(M-2)/sin(A*X)^(N-2),X)", "" },
	{ "1/(sin(A*X)^M*cos(A*X)^N)", "1/(A*(N-1)*sin(A*X)^(M-1)*cos(A*X)^(N-1))+(M+N-2)/(N-1)*integral(1/(sin(A*X)^M*cos(A*X)^(N-2)),X)", "" },
	{ "1/(cos(A*X)*(1+sin(A*X)))", "((sin(A*X)+1)*ln(sin(A*X)+1)-(sin(A*X)+1)*ln(sin(A*X)-1)-2)/(4*A*(sin(A*X)+1))", "" },
	{ "1/(cos(A*X)*(1+~1*sin(A*X)))", "((sin(A*X)-1)*ln(sin(A*X)+1)-(sin(A*X)-1)*ln(sin(A*X)-1)-2)/(4*A*(sin(A*X)-1))", "" },
	{ "1/(sin(A*X)*(1+~1*cos(A*X)))", "~1/(2*A*(1-cos(A*X)))+1/(2*A)*ln(tan(A*X/2))", "" },
	{ "1/(sin(A*X)*(1+cos(A*X)))", "1/(2*A*(1+cos(A*X)))+ln(tan(A*X/2))/(2*A)", "" },
	{ "1/(cos(A*X)+sin(A*X))", "sqrt(2)/(2*A)*ln(tan(A*X/2+PI/8))", "" },
	{ "1/(~1*cos(A*X)+sin(A*X))", "sqrt(2)/(2*A)*ln(tan(A*X/2-PI/8))", "" },
	{ "sin(A*X)/(cos(A*X)+sin(A*X))", "X/2-ln(cos(A*X)+sin(A*X))/(2*A)", "" },
	{ "sin(A*X)/(~1*cos(A*X)+sin(A*X))", "X/2+1/(2*A)*ln(~cos(A*X)+sin(A*X))", "" },
	{ "cos(A*X)/(cos(A*X)+sin(A*X))", "X/2+1/(2*A)*ln(cos(A*X)+sin(A*X))", "" },
	{ "cos(A*X)/(~1*cos(A*X)+sin(A*X))", "~X/2+1/(2*A)*ln(~cos(A*X)+sin(A*X))", "" },
	{ "sin(A*X)/(P+Q*cos(A*X))", "~ln(P+Q*cos(A*X))/(A*Q)", "" },
	{ "cos(A*X)/(P+Q*sin(A*X))", "ln(P+Q*sin(A*X))/(A*Q)", "" },
	{ "sin(A*X)/((P+Q*cos(A*X))^N)", "1/(A*Q*(N-1)*(P+Q*cos(A*X))^(N-1))", "" },
	{ "cos(A*X)/((P+Q*sin(A*X))^N)", "~1/(A*Q*(N-1)*(P+Q*sin(A*X))^(N-1))", "" },
	{ "1/(Q*cos(A*X)+P*sin(A*X))", "ln(tan((A*A+X*tan(Q/P))/2))/(A*sqrt(P^2+Q^2))", "" },
	{ "1/(Q+Q*cos(A*X)+P*sin(A*X))", "ln(Q+P*tan(A*X/2))/(A*P)", "" },
	{ "1/(R+Q*cos(A*X)+P*sin(A*X))", "2/(A*sqrt(R^2-P^2-Q^2))*atan((P+(R-Q)*tan(A*X/2))/sqrt(R^2-P^2-Q^2))", "" },
	{ "1/(sqrt(R)+Q*cos(A*X)+P*sin(A*X))", "(~1)/(A*sqrt(R))*tan(PI/4-(A*X+tan(Q/P))/2)", "R=P^2+Q^2" },
	{ "1/(~1*sqrt(R)+Q*cos(A*X)+P*sin(A*X))", "~tan(PI/4+(A*X+tan(Q/P))/2)/(A*sqrt(R))", "R=P^2+Q^2" },
	{ "1/(~Q*cos(A*X)^2+P*sin(A*X)^2)", "ln((sqrt(P)*tan(A*X)-sqrt(Q))/(sqrt(P)*tan(A*X)+sqrt(Q)))/(2*A*sqrt(P*Q))", "" },
	{ "1/(Q*cos(A*X)^2+P*sin(A*X)^2)", "atan((sqrt(P)*tan(A*X))/sqrt(Q))/(A*sqrt(P)*sqrt(Q))", "" },
	{ "cos(A*X)/(P*cos(A*X)+Q*sin(A*X))", "(P*X)/(P^2+Q^2)+Q/(A*(P^2+Q^2))*ln(Q*sin(A*X)+P*cos(A*X))", "" }
};

struct Integral Integralln[] =
{
	/* ln(A*X) */
	{ "ln(A*X)", "X*ln(A*X)-X", "" },
	{ "ln(A*X^M)", "X*ln(A*X^M)-M*X", "" },
	{ "ln(B+A*X)", "(X+B/A)*ln(B+A*X)-X", "" },
	{ "ln(~A+X^2)", "X*ln(~A+X^2)-2*sqrt(A)+X*ln((sqrt(A)+X)/(X-sqrt(A)))", "" },
	{ "ln(A+X^2)", "X*ln(A+X^2)-2*X+2*sqrt(A)*atan(X/sqrt(A))", "" },
	{ "ln(C+~A*X^2)", "(sqrt(A)*X*ln(~(A*X^2-C))-sqrt(C)*ln((sqrt(A)*X-sqrt(C))/(sqrt(A)*X+sqrt(C)))-2*sqrt(A)*X)/sqrt(A)", "" },
	{ "ln(C+A*X^2)", "(sqrt(A)*X*ln(A*X^2+C)+2*(sqrt(C)*atan(sqrt(A/C)*X)-sqrt(A)*X))/sqrt(A)", "" },
	{ "ln(C+B*X+A*X^2)", "1/A*sqrt(4*A*C-B^2)*atan((2*A*X)/sqrt(4*A*C-B^2))-2*X+(B/(2*A)+X)*ln(C+B*X+A*X^2)", "" },
	{ "X*ln(A*X)", "X^2/2*(ln(A*X)-1/2)", "" },
	{ "X^M*ln(A*X)", "X^(M+1)/(M+1)*(ln(A*X)-1/(M+1))", "" },
	{ "ln(A*X)^N", "X*ln(A*X)^N-N*integral(ln(A*X)^(N-1),X)", "" },
	{ "X^M*ln(A+X^2)", "X^(M+1)*ln(A+X^2)/(M+1)-2/(M+1)*integral(X^(M+2)/(A+X^2),X)", "" },
	{ "X*ln(B+A*X)", "B*X/(2*A)-X^2/4+1/2*(X^2-B^2/A^2)*ln(B+A*X)", "" },
	{ "1/(X*ln(A*X))", "ln(ln(A*X))", "" },
	{ "ln(A*X)/X", "ln(A*X)^2/2", "" },
	{ "ln(A*X)/X^M", "~ln(A*X)/((M-1)*X^(M-1))-1/((M-1)^2*X^(M-1))", "" },
	{ "ln(A*X)^N/X", "ln(A*X)^(N+1)/(N+1)", "" },
	{ "ln(A*X)^M/X^N", "~ln(A*X)^M/((N-1)*X^(N-1))+M/(N-1)*integral(ln(A*X)^(M-1)/(X^N),X)", "" },
	{ "ln(X+sqrt(~A+X^2))", "X*ln(X+sqrt(~A+X^2))-sqrt(~A+X^2)", "" },
	{ "X*ln(X+sqrt(~A+X^2))", "(X^2/2+A/4)*ln(X+sqrt(~A+X^2))-sqrt(~A+X^2)*X/4", "" },
	{ "X^N*ln(X+sqrt(~A+X^2))", "X^(N+1)/(N+1)*ln(X+sqrt(~A+X^2))-1/(N+1)*integral(X^(N+1)/sqrt(~A+X^2),X)", "" },
	{ "ln(X+sqrt(~A+X^2))/X^2", "~ln(X+sqrt(~A+X^2))/X-1/(sqrt(A)*acos(X/sqrt(A)))", "" },
	{ "ln(X+sqrt(~A+X^2))/X^3", "ln(X+sqrt(~A+X^2))/(2*X^2)+sqrt(~A+X^2)/(2*A*X)", "" },
	{ "ln(X+sqrt(~A+X^2))/X^N", "~ln(X+sqrt(~A+X^2))/((N-1)*X^(N-1))-1/(N-1)*integral(1/(X^(N-1)*sqrt(~A+X^2)),X)", "" },
	{ "ln(X+sqrt(A+X^2))", "X*ln(X+sqrt(A+X^2))-sqrt(A+X^2)", "" },
	{ "X*ln(X+sqrt(A+X^2))", "(X^2/2+A/4)*ln(X+sqrt(A+X^2))-sqrt(A+X^2)*X/4", "" },
	{ "X^N*ln(X+sqrt(A+X^2))", "X^(N+1)/(N+1)*ln(X+sqrt(A+X^2))-1/(N+1)*integral(X^(N+1)/sqrt(A+X^2),X)", "" },
	{ "ln(X+sqrt(A+X^2))/X^2", "~ln(X+sqrt(A+X^2))/X-ln((A+sqrt(A+X^2))/X)/sqrt(A)", "" },
	{ "ln(X+sqrt(A+X^2))/X^3", "~ln(X+sqrt(A+X^2))/(2*X^2)-sqrt(A+X^2)/(2*A*X)", "" },
	{ "ln(X+sqrt(A+X^2))/X^N", "~ln(X+sqrt(A+X^2))/((N-1)*X^(N-1))-1/(N-1)*integral(1/(X^(N-1)*sqrt(A+X^2)),X)", "" }
};

struct Integral Integralexp[] =
{
	/* exp(A*X) */
	{ "exp(B+A*X)", "exp(B+A*X)/A", "" },
	{ "X*exp(A*X)", "exp(A*X)/A*(X-1/A)", "" },
	{ "X*exp(A*X^2)", "exp(A*X^2)/(2*A)", "" },
	{ "X^3*exp(C+A*X^2)", "exp(A*X^2)*exp(C)*(X^2/A-1/A^2)/2", "" },
	{ "X^N*exp(B+A*X)", "X^N*exp(B+A*X)/A-N/A*integral(X^(N-1)*exp(B+A*X),X)", "" },
	{ "exp(A*X)*sin(A*X)", "exp(A*X)*(sin(A*X)-cos(A*X))/(2*A)", "" },
	{ "exp(A*X)*sin(B*X)", "exp(A*X)*(A*sin(B*X)-B*cos(B*X))/(A^2+B^2)", "" },
	{ "cos(A*X)*exp(A*X)", "exp(A*X)*(cos(A*X)+sin(A*X))/(2*A)", "" },
	{ "cos(B*X)*exp(A*X)", "exp(A*X)*(A*cos(B*X)+B*sin(B*X))/(A^2+B^2)", "" },
	{ "X*exp(A*X)*sin(B*X)", "X*exp(A*X)*(A*sin(B*X)-B*cos(B*X))/(A^2+B^2)-(exp(A*X)*((A^2-B^2)*sin(B*X)+2*A*B*cos(B*X)))/(A^2+B^2)^2", "" },
	{ "X*cos(B*X)*exp(A*X)", "X*exp(A*X)*(A*cos(B*X)+B*sin(B*X))/(A^2+B^2)-(exp(A*X)*((A^2-B^2)*cos(B*X)+2*A*B*sin(B*X)))/(A^2+B^2)^2", "" },
	{ "exp(A*X)*sin(B*X)^N", "exp(A*X)*sin(B*X)^(N-1)/(A^2+N^2*B^2)*(A*sin(B*X)-N*B*cos(B*X))+(N*(N-1)*B^2)/(A^2+N^2*B^2)*integral(exp(A*X)*sin(B*X)^(N-2),X)", "" },
	{ "cos(B*X)^N*exp(A*X)", "exp(A*X)*cos(B*X)^(N-1)/(A^2+N^2*B^2)*(A*cos(B*X)+N*B*sin(B*X))+(N*(N-1)*B^2)/(A^2+N^2*B^2)*integral(cos(B*X)^(N-2)*exp(A*X),X)", "" },
	{ "cosh(A*X)*exp(A*X)", "exp(2*A*X)/(4*A)+X/2", "" },
	{ "cosh(B*X)*exp(A*X)", "exp(A*X)/(A^2-B^2)*(A*cosh(B*X)-B*sinh(B*X))", "" },
	{ "exp(A*X)*sinh(A*X)", "exp(2*A*X)/(4*A)-X/2", "" },
	{ "exp(A*X)*sinh(B*X)", "exp(A*X)/(A^2-B^2)*(A*sinh(B*X)-B*cosh(B*X))", "" },
	{ "1/(P+Q*exp(A*X))", "X/P-ln(P+Q*exp(A*X))/(A*P)", "" },
	{ "1/(P+Q*exp(A*X))^2", "X/P^2+1/(A*P*(P+Q*exp(A*X)))-ln(P+Q*exp(A*X))/(A*P^2)", "" },
	{ "1/(P*exp(A*X)+Q*exp(~A*X))", "atan(sqrt(P/Q)*exp(A*X))/(A*sqrt(P*Q))", "" }
};

struct Integral Integralinvtrig[] =
{
	/* inverse trigo */
	{ "asin(X/A)", "X*asin(X/A)+sqrt(A^2-X^2)", "" },
	{ "asin(A*X)", "X*asin(A*X)+sqrt(1-A^2*X^2)", "" },
	{ "X*asin(X/A)", "(X^2/2-A^2/4)*asin(X/A)+(X*sqrt(A^2-X^2))/4", "" },
	{ "X*asin(A*X)", "(X^2/2-A^2/4)*asin(A*X)+(X*sqrt(1-A^2*X^2))/4", "" },
	{ "X^2*asin(X/A)", "X^3/3*asin(X/A)+((X^2+2*A^2)*sqrt(A^2-X^2))/9", "" },
	{ "X^2*asin(A*X)", "X^3/3*asin(A*X)+((X^2+2*A^2)*sqrt(1-A^2*X^2))/9", "" },
	{ "asin(X/A)/X^2", "~asin(X/A)/X-1/A*ln((A+sqrt(A^2-X^2))/X)", "" },
	{ "asin(A*X)/X^2", "~asin(A*X)/X-1/A*ln((A+sqrt(1-A^2*X^2))/X)", "" },
	{ "asin(X/A)^2", "X*asin(X/A)^2-2*X+2*sqrt(A^2-X^2)*asin(X/A)", "" },
	{ "asin(A*X)^2", "X*asin(A*X)^2-2*X+2*sqrt(1-A^2*X^2)*asin(A*X)", "" },
	{ "acos(X/A)", "X*acos(X/A)-sqrt(A^2-X^2)", "" },
	{ "acos(A*X)", "X*acos(A*X)-sqrt(1-A^2*X^2)", "" },
	{ "acos(X/A)^2", "X*acos(X/A)^2-2*X-2*sqrt(A^2-X^2)*acos(X/A)", "" },
	{ "acos(A*X)^2", "X*acos(A*X)^2-2*X-2/A*sqrt(1-A^2*X^2)*acos(A*X)", "" },
	{ "X*acos(X/A)", "(X^2/2-A^2/4)*acos(X/A)-(X*sqrt(A^2-X^2))/4", "" },
	{ "X*acos(A*X)", "(X^2/2-A^2/4)*acos(A*X)-(X*sqrt(1-A^2*X^2))/4", "" },
	{ "X^2*acos(X/A)", "X^3/3*acos(X/A)-((X^2+2*A^2)*sqrt(A^2-X^2))/9", "" },
	{ "X^2*acos(A*X)", "(3*A^3*X^3*acos(A*X)+(2-A^2*X^2)*sqrt(1-A^2*X^2))/(9*A^3)", "" },
	{ "X^M*acos(X/A)", "X^(M+1)/(M+1)*acos(X/A)+1/(M+1)*integral(X^(M+1)/sqrt(A^2-X^2),X)", "" },
	{ "X^M*acos(A*X)", "X^(M+1)/(M+1)*acos(A*X)+1/(M+1)*integral(X^(M+1)/sqrt(1-A^2*X^2),X)", "" },
	{ "acos(X/A)/X^2", "~acos(X/A)/X+1/A*ln((A+sqrt(A^2-X^2))/X)", "" },
	{ "acos(A*X)/X^2", "(2*A*X*ln(X)-2*A*X*ln(sqrt(1-A^2*X^2)-1)-2*acos(A*X))/(2*X)", "" },
	{ "asin(X/A)/acos(X/A)", "X*atan(X/A)-A/2*ln(A^2+X^2)", "" },
	{ "asin(A*X)/acos(A*X)", "(2*A*X*atan(A*X)-ln(A^2*X^2+1))/(2*A)", "" },
	{ "X*asin(X/A)/acos(X/A)", "(A^2+X^2)/2*atan(X/A)-A*X/2", "" },
	{ "X*asin(A*X)/acos(A*X)", "((A^2*X^2+1)*atan(A*X)-A*X)/(2*A^2)", "" },
	{ "X^2*asin(X/A)/acos(X/A)", "X^3/3*atan(X/A)-(A*X^2)/6+A^3/6*ln(A^2+X^2)", "" },
	{ "X^2*asin(A*X)/acos(A*X)", "(ln(A^2*X^2+1)+2*A^3*X^3*atan(A*X)-A^2*X^2)/(6*A^3)", "" },
	{ "asin(X/A)/(X^2*acos(X/A))", "~1/X*atan(X/A)-1/(2*A)*ln((A^2+X^2)/X^2)", "" },
	{ "asin(A*X)/(X^2*acos(A*X))", "~(A*X*ln((A^2*X^2+1)/X^2)+2*atan(A*X))/(2*X)", "" },
	{ "acos(X/A)/asin(X/A)", "X*atan(X/A)+A/2*ln(A^2+X^2)", "" },
	{ "acos(A*X)/asin(A*X)", "X*atan(A*X)+A/2*ln(A^2+X^2)", "" },
	{ "X*acos(X/A)/asin(X/A)", "(A^2+X^2)/(2*tan(X/A))+A*X/2", "" },
	{ "X^2*acos(X/A)/asin(X/A)", "X^3/(3*atan(X/A))+A/6*(X^2-A^2*ln(A^2+X^2))", "" },
	{ "X^2*acos(A*X)/asin(A*X)", "X^3/(3*atan(A*X))+X^2/(6*A)+1/(6*A^3)-ln(1+A^2*X^2)/(6*A^3)", "" },
	{ "X^M*asin(X/A)/acos(X/A)", "X^(M+1)/(M+1)*atan(X/A)-A/(M+1)*integral(X^(M+1)/(A^2+X^2),X)", "" },
	{ "X^M*asin(A*X)/acos(A*X)", "X^(M+1)/(M+1)*atan(A*X)-A/(M+1)*integral(X^(M+1)/(1+A^2*X^2),X)", "" },
	{ "X^M*acos(X/A)/asin(X/A)", "X^(M+1)/((M+1)*atan(X/A))+A/(M+1)*integral(X^(M+1)/(A^2+X^2),X)", "" },
	{ "X^M*acos(A*X)/asin(A*X)", "X^(M+1)/((M+1)*atan(A*X))+A/(M+1)*integral(X^(M+1)/(1+A^2*X^2),X)", "" }
};

struct Integral Integralcosh[] =
{
	/* cosh(A*X) */
	{ "cosh(B+A*X)", "sinh(B+A*X)/A", "" },
	{ "cosh(A*X)^N", "cosh(A*X)^(N-1)*sinh(A*X)/(A*N)+(N-1)/N*integral(cosh(A*X)^(N-2),X)", "" },
	{ "X*cosh(B+A*X)", "X*sinh(B+A*X)/A-cosh(B+A*X)/A^2", "" },
	{ "X*cosh(A*X)^2", "X^2/4+(X*sinh(2*A*X))/(4*A)-cosh(2*A*X)/(8*A^2)", "" },
	{ "X^M*cosh(B+A*X)", "X^M*sinh(B+A*X)/A-M/A*integral(X^(M-1)*sinh(B+A*X),X)", "" },
	{ "cosh(A*X)*cosh(B*X)", "sinh((A-B)*X)/(2*(A-B))+sinh((A+B)*X)/(2*(A+B))", "" },
	{ "cos(A*X)*cosh(B*X)", "(A*sin(A*X)*cosh(B*X)+B*cos(A*X)*sinh(B*X))/(A^2+B^2)", "" },
	{ "sin(A*X)*cosh(B*X)", "(B*sin(A*X)*sinh(B*X)-B*cos(A*X)*cosh(B*X))/(A^2+B^2)", "" },
	{ "1/cosh(A*X)", "2/A*atan(exp(A*X))", "" },
	{ "1/cosh(A*X)^N", "sinh(A*X)/(A*(N-1)*cosh(A*X)^(N-1))+(N-2)/(N-1)*integral(1/cosh(A*X)^2,X)", "" },
	{ "X/cosh(A*X)^N", "X*sinh(A*X)/(A*(N-1)*cosh(A*X)^(N-1))+1/((N-1)*(N-2)*A^2*cosh(A*X)^2)+(N-2)/(N-1)*integral(X/cosh(A*X)^2,X)", "" },
	{ "1/(1+cosh(A*X))", "tanh(A*X/2)/A", "" },
	{ "1/(~1+cosh(A*X))", "~1/(A*tanh(A*X/2))", "" },
	{ "X/(1+cosh(A*X))", "X/A*tanh(A*X/2)-2/A^2*ln(cosh(A*X/2))", "" },
	{ "X/(~1+cosh(A*X))", "~X/(A*tanh(A*X/2))+2/A^2*ln(sinh(A*X/2))", "" },
	{ "1/(1+cosh(A*X))^2", "tanh(A*X/2)/(2*A)-tanh(A*X/2)^3/(6*A)", "" },
	{ "1/(~1+cosh(A*X))^2", "1/(2*A*tanh(A*X/2))-1/(6*A*tanh(A*X/2)^3)", "" },
	{ "1/(P+Q*cosh(A*X))", "2/(A*sqrt(Q^2-P^2))*atan((Q*exp(A*X)+P)/sqrt(Q^2-P^2))", "" },
	{ "1/(P+Q*cosh(A*X))^2", "Q*sinh(A*X)/(A*(Q^2-P^2)*(P+Q*cosh(A*X)))-P/(Q^2-P^2)*integral(1/(P+Q*cosh(A*X)),X)", "" },
	{ "1/(P+Q*cosh(A*X)^2)", "ln((sqrt(P)*tanh(A*X)+sqrt(P+Q))/(sqrt(P)*tanh(A*X)-sqrt(P+Q)))/(2*A*sqrt(P*(P+Q)))", "" },
	{ "cosh(A*X)/(Q+P*cosh(A*X))", "X/Q-P/Q*integral(1/(P+Q*cosh(A*X)),X)", "" },
	{ "cosh(C*ln(A*x+B))", "1/(2*A)*(exp((C+1)*ln(A*x+B))/(C+1)+exp((1-C)*ln(A*x+B))/(1-C))", "" }
};

struct Integral Integralsinh[] =
{
	/* sinh(A*X) */
	{ "sinh(B+A*X)", "cosh(B+A*X)/A", "" },
	{ "sinh(A*X)^N", "sinh(A*X)^(N-1)*cosh(A*X)/(A*N)-(N-1)/N*integral(sinh(A*X)^(N-2),X)", "" },
	{ "X*sinh(B+A*X)", "X*cosh(B+A*X)/A-sinh(B+A*X)/A^2", "" },
	{ "X^M*sinh(B+A*X)", "X^M*cosh(B+A*X)/A-M/A*integral(X^(M-1)*cosh(B+A*X),X)", "" },
	{ "sinh(A*X)*sinh(B*X)", "sinh((A+B)*X)/(2*(A+B))-sinh((A-B)*X)/(2*(A-B))", "" },
	{ "sin(B*X)*sinh(A*X)", "(A*cosh(A*X)*sin(B*X)-B*sinh(A*X)*cos(B*X))/(A^2+B^2)", "" },
	{ "cos(B*X)*sinh(A*X)", "(A*cosh(A*X)*cos(B*X)+B*sinh(A*X)*sin(B*X))/(A^2+B^2)", "" },
	{ "1/sinh(A*X)", "ln(tanh(A*X)+1))/A", "" },
	{ "X*sinh(A*X)^2", "X*sinh(2*A*X)/(4*A)-cosh(2*A*X)/(8*A^2)-X^2/4", "" },
	{ "1/sinh(A*X)^2", "~1/(A*tanh(A*X))", "" },
	{ "1/(P+Q*sinh(A*X))", "1/(A*sqrt(P^2+Q^2))*ln((Q*exp(A*X)+P-sqrt(P^2+Q^2))/(Q*exp(A*X)+P+sqrt(P^2+Q^2)))", "" },
	{ "1/(P+Q*sinh(A*X))^2", "~Q*cosh(A*X)/(A*(P^2+Q^2)*(P+Q*sinh(A*X)))+P/(P^2+Q^2)*integral(1/(P+Q*sinh(A*X)),X)", "" },
	{ "1/(P+~Q*sinh(A*X)^2)", "1/(2*A*sqrt(P)*sqrt(P+Q))*ln((sqrt(P)+sqrt(P+Q)*tanh(A*X))/(sqrt(P)-sqrt(P+Q)*tanh(A*X)))", "" },
	{ "1/(P+Q*sinh(A*X)^2)", "1/(A*sqrt(P)*sqrt(Q-P))*atan((sqrt(Q-P)*tanh(A*X))/sqrt(P))", "" },
	{ "1/sinh(A*X)^N", "~cosh(A*X)/(A*(N-1)*sinh(A*X)^(N-1))-(N-2)/(N-1)*integral(1/sinh(A*X)^(N-2),X)", "" },
	{ "X/sinh(A*X)^N", "~X*cosh(A*X)/(A*(N-1)*sinh(A*X)^(N-1))-1/(A^2*(N-1)*(N-2)*sinh(A*X)^(N-2))-(N-2)/(N-1)*integral(X/sinh(A*X)^(N-2),X)", "" },
	{ "sinh(A*X)/(Q+P*sinh(A*X))", "X/Q-P/Q*integral(1/(P+Q*sinh(A*X)),X)", "" },
	{ "sinh(C*ln(A*X+B))", "1/(2*A)*(exp((C+1)*ln(A*X+B))/(C+1)-exp((1-C)*ln(A*X+B))/(1-C))", "" }
};

struct Integral Integraltrigh[] =
{
	/* sinh(A*X) && cosh(A*X)  */
	{ "cosh(A*X)*sinh(A*X)", "sinh(A*X)^2/(2*A)", "" },
	{ "cosh(A*X)*sinh(B*X)", "cosh((B+A)*X)/(2*(B+A))+cosh((B-A)*X)/(2*(B-A))", "" },
	{ "cosh(A*X)*sinh(A*X)^N", "sinh(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cosh(A*X)^N*sinh(A*X)", "cosh(A*X)^(N+1)/((N+1)*A)", "" },
	{ "cosh(A*X)^2*sinh(A*X)^2", "sinh(A*X)^4/(32*A)-X/8", "" },
	{ "1/(cosh(A*X)*sinh(A*X))", "ln(tanh(A*X))/A", "" },
	{ "1/(cosh(A*X)*sinh(A*X)^2)", "~atan(sinh(A*X))/A-1/(A*sinh(A*X))", "" },
	{ "1/(cosh(A*X)^2*sinh(A*X))", "1/(A*cosh(A*X))+1/A*ln(tanh(A*X/2))", "" },
	{ "1/(cosh(A*X)^2*sinh(A*X)^2)", "~2/(A*tanh(2*A*X))", "" },
	{ "sinh(A*X)^2/cosh(A*X)", "sinh(A*X)/A-1/A*atan(sinh(A*X))", "" },
	{ "cosh(A*X)^2/sinh(A*X)", "cosh(A*X)/A+1/A*ln(tanh(A*X/2))", "" },
	{ "1/(cosh(A*X)*(1+sinh(A*X)))", "ln((1+sinh(A*X))/cosh(A*X))/(2*A)+1/A*atan(exp(A*X))", "" },
	{ "1/(sinh(A*X)*(1+cosh(A*X)))", "ln(tanh(A*X/2))+1/(2*A*(1+cosh(A*X)))/(2*A)", "" },
	{ "1/(sinh(A*X)*(~1+cosh(A*X)))", "~ln(tanh(A*X/2)-1/(2*A*(cosh(A*X)-1)))/(2*A)", "" },
	/* tanh(A*X) */
	{ "sinh(A*X)/cosh(A*X)", "ln(cosh(A*X))/A", "" },
	{ "sinh(A*X)^2/cosh(A*X)^2", "X-tanh(A*X)/A", "" },
	{ "sinh(A*X)^3/cosh(A*X)^3", "ln(cosh(A*X))/A-sinh(A*X)^2/(2*A*cosh(A*X))", "" },
	{ "sinh(A*X)/cosh(A*X)^2", "ln(tanh(A*X))/A", "" },
	{ "X*sinh(A*X)^2/cosh(A*X)^2", "X^2/2-(X*tanh(A*X))/A+1/A^2*ln(cosh(A*X))", "" },
	{ "1/(P+Q*tanh(A*X))", "(P*X)/(P^2-Q^2)-Q/(A*(P^2-Q^2))*ln(Q*sinh(A*X)+P*cosh(A*X))", "" },
	{ "sinh(A*X)^N/cosh(A*X)^N", "~tanh(A*X)^(N-1)/(A*(N-1))+integral(sinh(A*X)^(N-2)/cosh(A*X)^(N-2),X)", "" },
	/* coth(A*X) */
	{ "cosh(A*X)/sinh(A*X)", "ln(sinh(A*X))/A", "" },
	{ "cosh(A*X)^2/sinh(A*X)^2", "X-1/(A*tanh(A*X))", "" },
	{ "cosh(A*X)/sinh(A*X)^3", "~tanh(A*X)^2/(2*A)", "" },
	{ "cosh(A*X)^2/sinh(A*X)^4", "~tanh(A*X)^3/(3*A)", "" },
	{ "cosh(A*X)^N/sinh(A*X)^(N+2)", "~tanh(A*X)^(N+1)/((N+1)*A)", "" },
	{ "sinh(A*X)^3/cosh(A*X)", "~ln(1/tanh(A*X))/A", "" },
	{ "X*cosh(A*X)^2/sinh(A*X)^2", "X^2/2-(X/tanh(A*X))/A+1/A^2*ln(sinh(A*X))", "" },
	{ "cosh(A*X)/(P*cosh(A*X)+Q*sinh(A*X))", "(P*X)/(P^2-Q^2)-Q/(A*(P^2-Q^2))*ln(P*sinh(A*X)+Q*cosh(A*X))", "" },
	{ "cosh(A*X)^N/sinh(A*X)^N", "~1/(A*(N-1)*tanh(A*X)^(N-1))+integral(cosh(A*X)^(N-2)/sinh(A*X)^(N-2),X)", "" },
	{ "sinh(A*X)/cosh(A*X)^N", "~1/(N*A*cosh(A*X)^N)", "" },
	{ "cosh(A*X)/sinh(A*X)^N", "~1/(N*A*sinh(A*X)^N)", "" }
};

struct Integral Integralinvtrigh[] =
{
	/* inverse trigo hyperbolique */
	{ "asinh(X/A)", "X*asinh(X/A)-sqrt(A^2+X^2)", "" },
	{ "asinh(A*X)", "X*asinh(A*X)-sqrt(1+A^2*X^2)/A", "" },
	{ "X*asinh(X/A)", "(X^2/2+A^2/4)*asinh(X/A)-X*sqrt(A^2+X^2)/4", "" },
	{ "X*asinh(A*X)", "((2*A^2*X^2-1)*asin(A*X)+A*X*sqrt(1-A^2*X^2))/(4*A^2)", "" },
	{ "X^2*asinh(X/A)", "X^3/3*asinh(X/A)+((2*A^2-X^2)*sqrt(A^2+X^2))/9", "" },
	{ "X^2*asinh(A*X)", "X^3*asinh(A*X)/3+(A^2*X^2+2)*sqrt(1-A^2*X^2)/(9*A^3)", "" },
	{ "asinh(X/A)/X^2", "~asinh(X/A)/X-1/A*ln((A+sqrt(A^2+X^2))/X)", "" },
	{ "asinh(A*X)/X^2", "A*ln((sqrt(1-A^2*X^2)-1)/X)-asin(A*X)/X", "" },
	{ "asinh(X/A)/acosh(X/A)", "~((X-A)*ln(~(X-A)/A)-(X+A)*ln((X+A)/A))/2", "" },
	{ "asinh(A*X)/acosh(A*X)", "~((A*X-1)*ln(~(A*X-1))-(A*X+1)*ln(A*X+1))/(2*A)", "" },
	{ "X*asinh(X/A)/acosh(X/A)", "~(X^2*ln(~(X-A)/A)-X^2*ln((X+A)/A)-A*(A*ln(X-A)-A*ln(X+A)+2*X))/4", "" },
	{ "X*asinh(A*X)/acosh(A*X)", "~(A^2*X^2*ln(~(A*X-1))-(A^2*X^2-1)*ln(A*X+1)-ln(A*X-1)-2*A*X)/(4*A^2)", "" },
	{ "X^2*asinh(X/A)/acosh(X/A)", "~(X^3*ln(~(X-A)/A)-X^3*ln((X+A)/A)-A*(A^2*ln(X-A)+A^2*ln(X+A)+X^2))/6", "" },
	{ "X^2*asinh(A*X)/acosh(A*X)", "~(A^3*X^3*ln(~(A*X-1))-(A^3*X^3+1)*ln(A*X+1)-ln(A*X-1)-A^2*X^2)/(6*A^3)", "" },
	{ "asinh(X/A)/(X^2*acosh(X/A))", "(A*ln(~(X-A)/A)-A*ln((X+A)/A)-X*(ln(X-A)+ln(X+A)-2*ln(X)))/(2*A*X)", "" },
	{ "asinh(A*X)/(X^2*acosh(A*X))", "(ln(~(A*X-1))-(A*X+1)*ln(A*X+1)-A*X*(ln(A*X-1)-2*ln(X)))/(2*X)", "" },
	{ "acosh(X/A)/asinh(X/A)", "(X*ln((X+A)/(X-A))+A*(ln(X-A)+ln(X+A)))/2", "" },
	{ "acosh(A*X)/asinh(A*X)", "(A*X*ln((A*X+1)/(A*X-1))+ln(A*X+1)+ln(A*X-1))/(2*A)", "" },
	{ "X*acosh(X/A)/asinh(X/A)", "(X^2*ln((X+A)/(X-A))+A*(A*ln(X-A)-A*ln(X+A)+2*X))/4", "" },
	{ "X*acosh(A*X)/asinh(A*X)", "(A^2*X^2*ln((A*X+1)/(A*X-1))-ln(A*X+1)+ln(A*X-1)+2*A*X)/(4*A^2)", "" },
	{ "X^2*acosh(X/A)/asinh(X/A)", "(X^3*ln((X+A)/(X-A))+A*(A^2*ln(X-A)+A^2*ln(X+A)+X^2))/6", "" },
	{ "X^2*acosh(A*X)/asinh(A*X)", "(A^3*X^3*ln((A*X+1)/(A*X-1))+ln(A*X+1)+ln(A*X-1)+A^2*X^2)/(6*A^3)", "" },
	{ "acosh(X/A)/(X^2*asinh(X/A))", "~(A*ln((X+A)/(X-A))+X*(ln(X-A)+ln(X+A)-2*ln(X)))/(2*A*X)", "" },
	{ "acosh(A*X)/(X^2*asinh(A*X))", "~(ln((A*X+1)/(A*X-1))+A*X*(ln(A*X+1)+ln(A*X-1)-2*ln(X)))/(2*X)", "" },
	{ "X^M*asinh(X/A)", "X^(M+1)/(M+1)*asinh(X/A)-integral(X^(M+1)/sqrt(A^2+X^2),X)/(M+1)", "" },
	{ "X^M*asinh(A*X)", "X^(M+1)/(M+1)*asinh(A*X)-integral(X^(M+1)/sqrt(1+A^2*X^2),X)/(M+1)", "" },
	{ "X^M*asinh(X/A)/acosh(X/A)", "X^(M+1)/(M+1)*atanh(X/A)-A/(M+1)*integral(X^(M+1)/(A^2-X^2),X)", "" },
	{ "X^M*asinh(A*X)/acosh(A*X)", "X^(M+1)/(M+1)*atanh(A*X)-A/(M+1)*integral(X^(M+1)/(1-A^2*X^2),X)", "" },
	{ "X^M*acosh(X/A)/asinh(X/A)", "X^(M+1)/((M+1)*atanh(X/A))-A/(M+1)*integral(X^(M+1)/(A^2-X^2),X)", "" },
	{ "X^M*acosh(A*X)/asinh(A*X)", "X^(M+1)/((M+1)*atanh(A*X))-A/(M+1)*integral(X^(M+1)/(1-A^2*X^2),X)", "" }
};

struct Integral Integraltable[] =
{
	{ "1/X", "ln(X)", "" },
	{ "1/X^M", "~1/((M-1)*X^(M-1))", "" },
	{ "A^X", "A^X/ln(A)", "" },
	{ "A^(Q+P*X)", "A^(Q+P*X)/(P*ln(A))", "" },
	/* A*X+B */
	{ "(B+A*X)^N", "(B+A*X)^(N+1)/((N+1)*A)", "" },
	{ "X*(B+A*X)^N", "(B+A*X)^(N+2)/((N+2)*A^2)-B*(B+A*X)^(N+1)/((N+1)*A^2)", "" },
	{ "X^M*(B+A*X)^N", "X^(M+1)*(A*X+B^N)/(M+N+1)+N*B/(M+N+1)*integral(X^M*(B+A*X)^(N-1),X)", "" },
	{ "1/(B+A*X)", "ln(B+A*X)/A", "" },
	{ "X/(B+A*X)", "X/A-B/A^2*ln(B+A*X)", "" },
	{ "X^2/(B+A*X)", "(B+A*X)^2/(2*A^3)-2*B*(B+A*X)/A^3+B^3/A^3*ln(B+A*X)", "" },
	{ "X^3/(B+A*X)", "(B+A*X)^3/(3*A^4)-3*B*(B+A*X)^2/2*A^4+(3*B^2*(B+A*X))/A^4-B^3/A^4*ln(B+A*X)", "" },
	{ "1/(B+A*X)^2", "~1/(A*(B+A*X))", "" },
	{ "X/(B+A*X)^2", "B/(A^2*(B+A*X))+1/A^2*ln(B+A*X)", "" },
	{ "X^2/(B+A*X)^2", "(B+A*X)/A^3-B^2/(A^3*(B+A*X))-2*B/A^3*ln(B+A*X)", "" },
	{ "X^3/(B+A*X)^2", "(B+A*X)^2/(2*A^4)-(3*B*(B+A*X))/A^4+B^3/(A^4*(B+A*X))+3*B^2/A^4*ln(B+A*X)", "" },
	{ "1/(B+A*X)^3", "~1/(2*(B+A*X)^2)", "" },
	{ "X/(B+A*X)^3", "~1/(A^2*(B+A*X))+B/(2*A^2*(A*X+B^2))", "" },
	{ "X^2/(B+A*X)^3", "2*B/(A^3*(B+A*X))-B^2/(2*A^3*(B+A*X)^2)+ln(B+A*X)/A^3", "" },
	{ "X^3/(B+A*X)^3", "X/A^3-3*B^2/(A^4*(B+A*X))+B^3/(2*A^4*(B+A*X)^2)-3*B/A^4*ln(B+A*X)", "" },
	{ "(B+A*X)/(Q+P*X)", "A*X/P+(B*P-A*Q)/P^2*ln(Q+P*X)", "" },
	{ "(B+A*X)^M/(Q+P*X)^N", "~1/((N-1)*(B*P-A*Q))*((B+A*X)^(M+1)/(Q+P*X)^(N-1)+(N-M-2)*A*integral((B+A*X)^M/(Q+P*X)^(N-1),X))", "" },
	{ "1/(X*(B+A*X))", "ln(X/(B+A*X))/B", "" },
	{ "1/(X^2*(B+A*X))", "~1/(B*X)+A/B^2*ln((B+A*X)/X)", "" },
	{ "1/(X^3*(B+A*X))", "(2*A*X-B)/(2*B^2*X^2)+A^2/B^3*ln(X/(B+A*X))", "" },
	{ "1/(X*(B+A*X)^2)", "1/(B*(B+A*X))+1/B^2*ln(X/(B+A*X))", "" },
	{ "1/(X^2*(B+A*X)^2)", "~A/(B^2*(B+A*X))-1/(B^2*X)+2*A/B^3*ln((B+A*X)/X)", "" },
	{ "1/(X^3*(B+A*X)^2)", "~(B+A*X)^2/(2*B^4*X^2)+3*A*(B+A*X)/(B^4*X)-A^3*X/(B^4*(B+A*X))-3*A^2/B^4*ln((B+A*X)/X)", "" },
	{ "1/(X*(B+A*X)^3)", "A^2*X^2/(2*B^3*(B+A*X)^2)-2*A*X/(B^3*(B+A*X))-ln((B+A*X)/X)/B^3", "" },
	{ "1/(X^2*(B+A*X)^3)", "~A/(2*B^2*(B+A*X)^2)-2*A/(B^3*(B+A*X))-1/(B^3*X)+3*A/B^4*ln((B+A*X)/X)", "" },
	{ "1/(X^3*(B+A*X)^3)", "A^4*X^2/(2*B^5(B+A*X)^2)-(4*A^3*X)/(B^5*(B+A*X))-(B+A*X)^2/(2*B^5*X^2)-6*A^2/B^5*ln((B+A*X)/X)", "" },
	/*(B+A*X) & (Q+P*X) */
	{ "1/((B+A*X)*(Q+P*X))", "ln((Q+P*X)/(B+A*X))/(B*P-A*Q)", "" },
	{ "X/((B+A*X)*(Q+P*X))", "(B/A*ln((B+A*X)-Q/P*ln(Q+P*X)))/(B*P-A*Q)", "" },
	{ "1/((Q+P*X)*(B+A*X)^2)", "(1/(B+A*X)+P/(B*P-A*Q)*ln((Q+P*X)/(B+A*X)))/(B*P-A*Q)", "" },
	{ "X/((Q+P*X)*(B+A*X)^2)", "(Q/(B*P-A*Q)*ln((B+A*X)/(Q+P*X))-B/(A*(B+A*X)))/(B*P-A*Q)", "" },
	{ "X^2/((Q+P*X)*(B+A*X)^2)", "B^2/((B*P-A*Q)*A^2*(B+A*X))+1/(B*P-A*Q)^2*(Q^2/P*ln(Q+P*X)+B*(B*P-2*A*Q)/A^2*ln(B+A*X))", "" },
	{ "1/((B+A*X)^M*(Q+P*X)^N)", "~(1/((B+A*X)^(M-1)*(Q+P*X)^(N-1))+A*(M+N-2)*integral(1/((B+A*X)^M*(Q+P*X)^(N-1)),X))/((N-1)*(B*P-A*Q))", "" },
};

struct Integral Integralalgx2[] =
{
	/* C+A*X^2 */
	{ "1/(~C+A*X^2)", "1/(2*sqrt(A*C))*ln((X*sqrt(A)-sqrt(C))/(X*sqrt(A)+sqrt(C)))", "" },
	{ "1/(C+~A*X^2)", "1/(2*sqrt(A*C))*ln((X*sqrt(A)+sqrt(C))/(X*sqrt(A)-sqrt(C)))", "" },
	{ "1/(C+A*X^2)", "atan(X*sqrt(A/C))/sqrt(A*C)", "" },
	{ "1/(C+A*X^2)^N", "X/((2*(N-1)*C)*(A*X^2+C)^(N-1))+(2*N-3)/(2*(N-1)*C)*integral(1/(C+A*X^2)^(N-1),X)", "" },
	{ "X/(C+A*X^2)", "ln(C+A*X^2)/(2*A)", "" },
	{ "X/(C+A*X^2)^N", "~1/(2*A*(N-1)*(C+A*X^2)^(N-1))", "" },
	{ "X*(C+A*X^2)^N", "(A*X^2+C)^(N+1)/(2*A*(N+1))", "" },
	{ "X^M/(C+A*X^2)", "X^(M-1)/(A*(M-1))-C/A*integral(X^(M-2)/(C+A*X^2),X)", "" },
	{ "1/(X*(C+A*X^N))", "ln(X^N/(C+A*X^N))/(C*N)", "" }
};

struct Integral Integralalgx3[] =
{
	/* A^3+X^3 */
	{ "1/(A+X^3)", "1/(6*A^(2/3))*ln((cbrt(A)+X)^2/(A^(2/3)-cbrt(A)*X+X^2))+1/(A^(2/3)*sqrt(3))*atan((2*X-cbrt(A))/(cbrt(A)*sqrt(3)))", "" },
	{ "X/(A+X^3)", "1/(6*cbrt(A))*ln((A^(2/3)-cbrt(A)*X+X^2)/(cbrt(A)+X)^2)+1/(cbrt(A)*sqrt(3))*atan((2*X-cbrt(A))/(cbrt(A)*sqrt(3)))", "" },
	{ "X^2/(A+X^3)", "ln(A+X^3)/3", "" },
	{ "1/(X*(A+X^3))", "ln(X^3/(A+X^3))/(3*A)", "" },
	{ "1/(X^2*(A+X^3))", "~1/(A*X)-1/(6*A^(4/3))*ln((A^(2/3)-cbrt(A)*X+X^2)/(cbrt(A)+X)^2)-1/(A^(4/3)*sqrt(3))*atan((2*X-cbrt(A))/(cbrt(A)*sqrt(3)))", "" },
	{ "1/(A+X^3)^2", "X/(3*A^(2/3)*(A+X^3))+1/(9*A^(5/3))*ln((cbrt(A)+X)^2/(A^(2/3)-cbrt(A)*X+X^2))+2/(3*A^(5/3)*sqrt(3))*atan((2*X-cbrt(A))/(cbrt(A)*sqrt(3)))", "" },
	{ "X/(A+X^3)^2", "X^2/(3*A*(A+X^3))+1/(18*A^(4/3))*ln((A^(2/3)-cbrt(A)*X+X^2)/(cbrt(A)+X)^2)+1/(3*A^(4/3)*sqrt(3))*atan((2*X-cbrt(A))/(cbrt(A)*sqrt(3)))", "" },
	{ "X^2/(A+X^3)^2", "~1/(3*(A+X^3))", "" },
	{ "1/(X*(A+X^3)^2)", "1/(3*A*(A+X^3))+ln(X^3/(A+X^3))/(3*A^2)", "" },
	{ "1/(X^2*(A+X^3)^2)", "~1/(A^2*X)-X^2/(3*A^2*(A+X^3))-4/(3*A^2)*integral(X/(A+X^3),X)", "" },
	{ "X^M/(A+X^3)", "X^(M-2)/(M-2)-A*integral(X^(M-3)/(A+X^3),X)", "" },
	{ "1/(X^N*(A+X^3))", "(~1)/(A*(N-1)X^(N-1))-integral(1/(X^(N-3)*(A+X^3)),X)/A", "" }
};

struct Integral Integralalgx4[] =
{
	/* X^4+-A^4 */
	{ "1/(~A+X^4)", "1/(4*A^(3/4))*ln((X-A^(1/4))/(A^(1/4)+X))-1/(2*A^(3/4))*atan(X/A^(1/4))", "" },
	{ "X/(~A+X^4)", "1/(4*sqrt(A))*ln((~sqrt(A)+X^2)/(sqrt(A)+X^2))", "" },
	{ "X^2/(~A+X^4)", "ln((X-A^(1/4))/(A^(1/4)+X))/(4*A^(1/4))+atan(X/A^(1/4))/(2*A^(1/4))", "" },
	{ "X^3/(~A+X^4)", "ln(~A+X^4)/4", "" },
	{ "1/(X*(~A+X^4))", "ln((~A+X^4)/X^4)/(4*A)", "" },
	{ "1/(X^2*(~A+X^4))", "1/(A*X)+ln((X-A^(1/4))/(A^(1/4)+X))/(4*A^(5/4))+atan(X/A^(1/4))/(2*A^(5/4))", "" },
	{ "1/(X^3*(~A+X^4))", "1/(2*A*X^2)+1/(4*A^(3/2))*ln((~sqrt(A)+X^2)/(sqrt(A)+X^2))", "" },
	{ "1/(A+X^4)", "1/(4*A^(3/4)*sqrt(2))*ln((X^2+A^(1/4)*X*sqrt(2)+sqrt(A))/(X^2-A^(1/4)*X*sqrt(2)+sqrt(A)))-1/(2*A^(3/4)*sqrt(2))*atan((A^(1/4)*X*sqrt(2))/(~sqrt(A)+X^2))", "" },
	{ "X/(A+X^4)", "atan(X^2/sqrt(A))/(2*sqrt(A))", "" },
	{ "X^2/(A+X^4)", "1/(4*A^(1/4)*sqrt(2))*ln((X^2-A^(1/4)*X*sqrt(2)+sqrt(A))/(X^2+A^(1/4)*X*sqrt(2)+sqrt(A)))-1/(2*A^(1/4)*sqrt(2))*atan((A^(1/4)*X*sqrt(2))/(~sqrt(A)+X^2))", "" },
	{ "X^3/(A+X^4)", "ln(A+X^4)/4", "" },
	{ "1/(X*(A+X^4))", "ln(X^4/(A+X^4))/(4*A)", "" },
	{ "1/(X^2*(A+X^4))", "~1/(A*X)-1/(4*A^(5/4)*sqrt(2))*ln((X^2-A^(1/4)*X*sqrt(2)+sqrt(A))/(X^2+A^(1/4)*X*sqrt(2)+sqrt(A)))+1/(2*A^(5/4)*sqrt(2))*atan((A^(1/4)*X*sqrt(2))/(~sqrt(A)+X^2))", "" },
	{ "1/(X^3*(A+X^4))", "~1/(2*A*X^2)-atan(X^2/sqrt(A))/(2*A^(3/2))", "" }
};

struct Integral IntegralalgxN[] =
{
	/* X^N+-A^N */
	{ "1/(X*(~A+X^N))", "ln((~A+X^N)/X^N)/(N*A)", "" },
	{ "X^M/(~A+X^N)", "ln(~A+X^N)/N", "M=N-1"},
	{ "X^M/(~A+X^N)^R", "A*integral(X^(M-N)/(~A+X^N)^R,X)+integral(X^(M-N)/(~A+X^N)^(R-1),X)", "" },
	{ "1/(X^M*(~A+X^N)^R)", "integral(1/(X^(M-N)*(~A+X^N)^R),X)/A-1/A*integral(1/(X^M*(~A+X^N)^(R-1)),X)", "" },
	{ "1/(X*sqrt(~A+X^N))", "2/(N*sqrt(A))*acos(sqrt(A/X^N))", "" },
	{ "1/(X*(A+X^N))", "ln(X^N/(A+X^N))/(N*A)", "" },
	{ "X^M/(A+X^N)", "ln(A+X^N)/N", "M=N-1" },
	{ "X^M/(A+X^N)^R", "integral(X^(M-N)/(A+X^N)^(R-1),X)-A*integral(X^(M-N)/(A+X^N)^R,X)", "" },
	{ "1/(X^M*(A+X^N)^R)", "integral(1/(X^M*(A+X^N)^(R-1)),X)/A-integral(1/(X^(M-N)*(A+X^N)^R),X)/A", "" },
	{ "1/(X*sqrt(A+X^N))", "ln((sqrt(A+X^N)-sqrt(A))/(sqrt(A+X^N)+sqrt(A)))/(N*sqrt(A))", "" }
};

struct Integral Integralalgx22[] =
{
	/* A*X ^ 2 + B*X + C */
	{ "1/(C+B*X+A*X^2)", "2/(2*A*X+B)", "B^2=4*A*C" },
	{ "1/(C+B*X+A*X^2)", "2/sqrt(4*A*C-B^2)*atan((2*A*X+B)/sqrt(4*A*C-B^2))", "B^2<4*A*C" },
	{ "1/(C+B*X+A*X^2)", "1/sqrt(B^2-4*A*C)*ln(2*A*X+B-sqrt(B^2-4*A*C))/(2*A*X+B+sqrt(B^2-4*A*C))", "" },
	{ "1/(C+B*X+A*X^2)^N", "(B+2*A*X)/((N-1)*(4*A*C-B^2)*(C+B*X+A*X^2)^(N-1))+2*(2*(N-1)-1)*A/((N-1)*(4*A*C-B^2))*integral(1/(C+B*X+A*X^2)^(N-1),X)", "" },
	{ "X/(C+B*X+A*X^2)", "1/(2*A)*ln(C+B*X+A*X^2)-B/(2*A)*integral(1/(C+B*X+A*X^2),X)", "" },
	{ "X^2/(C+B*X+A*X^2)", "X/A-B/(2*A^2)*ln(C+B*X+A*X^2)+(B^2-2*A*C)/(2*A^2)*integral(1/(C+B*X+A*X^2),X)", "" },
	{ "X^M/(C+B*X+A*X^2)", "X^(M-1)/((M-1)*A)-C/A*integral(X^(M-2)/(C+B*X+A*X^2),X)-B/A*integral(X^(M-1)/(C+B*X+A*X^2),X)", "" },
	{ "1/(X*(C+B*X+A*X^2))", "ln(X^2/(C+B*X+A*X^2))/(2*C)-B/(2*C)*integral(1/(C+B*X+A*X^2),X)", "" },
	{ "1/(X^N*(C+B*X+A*X^2))", "~1/((N-1)*C*X^(N-1))-B/C*integral(1/(X^(N-1)*(C+B*X+A*X^2)),X)-A/C*integral(1/(X^(N-2)*(C+B*X+A*X^2)),X)", "" },
	{ "1/(C+B*X+A*X^2)^2", "(2*A*X+B)/((4*A*C-B^2)*(C+B*X+A*X^2))+(2*A)/(4*A*C-B^2)*integral(1/(C+B*X+A*X^2),X)", "" },
	{ "X/(C+B*X+A*X^2)^2", "~(B*X+2*C)/((4*A*C-B^2)*(C+B*X+A*X^2))-B/(4*A*C-B^2)*integral(1/(C+B*X+A*X^2),X)", "" },
	{ "X^2/(C+B*X+A*X^2)^2", "((B^2-2*A*C)X+B*C)/(A*(4*A*C-B^2)*(C+B*X+A*X^2))+(2*C)/(4*A*C-B^2)*integral(1/(C+B*X+A*X^2),X)", "" },
	{ "X^M/(C+B*X+A*X^2)^N", "1/A*integral(X^(2*N-3)/(C+B*X+A*X^2)^(N-1),X)-C/A*integral(X^(2*N-3)/(C+B*X+A*X^2)^N,X)-B/A*integral(X^(2*N-2)/(C+B*X+A*X^2)^N,X)", "M=2*N-1" },
	{ "X^M/(C+B*X+A*X^2)^N", "~X^(M-1)/((2*N-M-1)*A*(C+B*X+A*X^2)^(N-1))+((M-1)*C)/((2*N-M-1)*A)*integral(X^(M-2)/(C+B*X+A*X^2)^N,X)-((N-M)*B)/((2*N-M-1)*A)*integral(X^(M-1)/(C+B*X+A*X^2)^N,X)", "" },
	{ "1/(X*(C+B*X+A*X^2)^N)", "1/(2*C*(N-1)*(C+B*X+A*X^2)^(N-1))-B/(2*C)*integral(1/(C+B*X+A*X^2)^N,X)+1/C*integral(1/(X*(C+B*X+A*X^2)^(N-1)),X)", "" },
	{ "1/(X^2*(C+B*X+A*X^2)^2)", "~1/(C*X*(C+B*X+A*X^2))-(3*A)/C*integral(1/(C+B*X+A*X^2)^2,X)-(2*B)/C*integral(1/(X*(C+B*X+A*X^2)^2),X)", "" },
	{ "1/(X^M*(C+B*X+A*X^2)^N)", "~1/((M-1)*C*X^(M-1)*(C+B*X+A*X^2)^(N-1))-((M+2*N-3)*A)/((M-1)*C)*integral(1/(X^(M-2)*(C+B*X+A*X^2)^N),X)-((M+N-2)*B)/((M-1)*C)*integral(1/(X^(M-1)*(C+B*X+A*X^2)^N),X)", "" }
};
