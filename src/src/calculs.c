#include "includes.h"

List Error = NULL;
bool INTEGRATE = true;

const char* err_msg[] = { "Err: Args", "Err: No solution", "Err: Args Conditions" };

static Tree* diff_n(Tree* tr, const char* vr, int k)
{
	Tree* res = clone(tr);
	for (int i = 0; i < k; i++)
	{
		Tree* tmp = diff(res, vr);
		clean_tree(res);
		res = simplify(tmp);
	}
	return res;
}

static Tree* diff_partial(Tree* tr, const char* vr, const char* vr1)
{
	return simplify(join(diff(tr, vr), diff(tr, vr1), fnc[ADD].ex));
}

static Tree* tangline(Tree* tr, const char* vr, Tree* point)
{
	Tree* dtr = diff(tr, vr);
	Tree* dtrc = remplace_tree(dtr, vr, point), * trc = remplace_tree(tr, vr, point);
	Tree* tantr = join(join(dtrc, join(new_tree(vr), clone(point), fnc[SUB].ex), fnc[PROD].ex), trc, fnc[ADD].ex);
	clean_tree(dtr);
	return simplify(tantr);
}

static List eqd_extract(Tree* eq, char* y2, char* y1, char* y0)
{
	Tree* tr = simplify(join(clone(eq->tleft), clone(eq->tright), fnc[SUB].ex));
	List cf = push_back(push_back(push_back(NULL, coefficient_gpe(tr, y2, 1)), coefficient_gpe(tr, y1, 1)), coefficient_gpe(tr, y0, 1));
	Tree* o = coefficient_gpe(tr, y2, 0);
	clean_tree(tr);
	Tree* p = coefficient_gpe(o, y1, 0);
	clean_tree(o);
	cf = push_back(cf, simplify(join(coefficient_gpe(p, y0, 0), NULL, fnc[NEGATIF].ex)));
	clean_tree(p);
	return cf;
}

/* analyse */

static map analyse_separe(Tree* tr)
{
	map L = NULL;
	Tree* t;
	for (t = tr; t->tok_type == SEPARATEUR; t = t->tleft)
		L = push_front_map(L, t->tright);
	L = push_front_map(L, t);
	return L;
}

Tree* analyse_rules(Tree* tr)
{
	token tk = tr->tok_type;
	if (tk == EXPAND_F)
	{
		TRIG_EXPAND = true;
		LN_EXP_EXPAND = true;
		ALG_EXPAND = true;
		Tree* s = algebraic_expand(tr->tleft);
		clean_noeud(tr);
		return simplify(s);
	}
	else if (tk == FACTOR_F)
	{
		if (tr->tleft->tok_type == SEPARATEUR && tr->tleft->tright->gtype == VAR && ispoly(tr->tleft->tleft, tr->tleft->tright->value))
		{
            map coefs = polycoeffs(tr->tleft->tleft, tr->tleft->tright->value);
			Tree* s = pfactor(coefs, tr->tleft->tright->value);
			clean_tree(tr);
			return s;
		}
		tr->tleft = simplify(tr->tleft);
		if (tr->tleft->gtype == ENT)
		{
			Tree* u = factorn(tonumber(tr->tleft->value));
			clean_tree(tr);
			return u;
		}
		if (is_int(tr->tleft))
		{
			Tree* u = factorn(tonumber(tr->tleft->tleft->value));
			clean_tree(tr);
			return join(u, NULL, fnc[NEGATIF].ex);
		}
		return tr;
	}
	else if (DERIV_F <= tk && tk <= TAYLOR_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if (tk == DERIV_F && ((L->length == 2 && ((Tree*)L->end->data)->gtype == VAR) || (L->length == 3 && ((Tree*)L->end->back->data)->gtype == VAR && (((Tree*)L->end->data)->gtype == VAR || ((Tree*)L->end->data)->gtype == ENT))))
		{
			Tree* res = NULL;
			if (((Tree*)L->end->data)->gtype == ENT)
				res = simplify(diff_n(L->begin->data, ((Tree*)L->end->back->data)->value, (int)tonumber(((Tree*)L->end->data)->value)));
			else if (L->length == 2 || !strcmp(((Tree*)L->end->back->data)->value, ((Tree*)L->end->data)->value))
				res = simplify(diff(L->begin->data, ((Tree*)L->end->data)->value));
			else
				res = simplify(diff_partial(L->begin->data, ((Tree*)L->end->back->data)->value, ((Tree*)L->end->data)->value));
			L = clear_map(L);
			return res;
		}
		else if (tk == TAYLOR_F && L->length == 4 && ((Tree*)L->begin->next->data)->gtype == VAR && ((Tree*)L->end->back->data)->gtype == ENT)
		{
			Tree* res = taylor(L->begin->data, L->begin->next->data, L->end->back->data, L->end->data);
			L = clear_map(L);
			return res;
		}
		else if (tk == TANG_F && L->length == 3 && ((Tree*)L->begin->next->data)->gtype == VAR)
		{
			Tree* res = tangline(L->begin->data, ((Tree*)L->begin->next->data)->value, L->end->data);
			L = clear_map(L);
			return simplify(res);
		}
		else if (tk == INTEGRAL_F && L->length >= 2 && ((Tree*)L->begin->next->data)->gtype == VAR)
		{
			L->begin->data = pow_transform(simplify(L->begin->data));
			Tree* res = integral(L->begin->data, ((Tree*)L->begin->next->data)->value);
			L = clear_map(L);
			if (res == NULL)
			{
				Error = push_back_dlist(Error, err_msg[1]);
				return NULL;
			}
			return simplify(res);
		}
		else if (tk == DESOLVE_F && L->length == 3 && ((Tree*)L->begin->next->data)->gtype == VAR && ((Tree*)L->end->data)->gtype == VAR)
		{
			Tree* t = L->begin->data, * x = L->begin->next->data, * y = L->end->data, * cond1 = NULL, * cond2 = NULL;
			char y2[5], y1[5], var_y[5], var_x[5];
			sprintf(y2, "%s''", y->value);
			sprintf(y1, "%s'", y->value);
			strcpy(var_x, x->value);
			strcpy(var_y, y->value);
			if (!found_element(t, y2))
			{
				if (t->tok_type == LOGIC_AND)
				{
					cond1 = clone(t->tright);
					t = t->tleft;
				}
				List cfs = eqd_extract(t, y2, y1, y->value);
				L = clear_map(L);
				Tree* rt = solve_ode(clone(cfs->begin->next->data), clone(cfs->end->back->data), clone(cfs->end->data), var_x, var_y, cond1);
				cfs = clear_map(cfs);
				return rt;
			}
			if (t->tok_type == LOGIC_AND)
			{
				if (t->tleft->tok_type != LOGIC_AND)
				{
					L = clear_map(L);
					Error = push_back_dlist(Error, err_msg[2]);
					return NULL;
				}
				cond2 = clone(t->tright);
				t = t->tleft;
				cond1 = clone(t->tright);
				t = t->tleft;
			}
			List cfs = eqd_extract(t, y2, y1, y->value);
			L = clear_map(L);
			Tree* rt = solve_ode_2(clone(cfs->begin->data), clone(cfs->begin->next->data), clone(cfs->end->back->data), clone(cfs->end->data), var_x, var_y, cond1, cond2);
			cfs = clear_map(cfs);
			return rt;
		}
		else if (REMAINDER_F <= tk && tk <= POLYSIMP_F && L->length == 3 && ((Tree*)L->end->data)->gtype == VAR)
		{
			map coef_t = polycoeffs(L->begin->data, ((Tree*)L->end->data)->value), coef_a = polycoeffs(L->begin->next->data, ((Tree*)L->end->data)->value), r = NULL;
			if (tk == POLYSIMP_F)
			{
				Tree* ret = poly_simp(coef_t, coef_a, ((Tree*)L->end->data)->value);
				L = clear_map(L);
				return ret;
			}
			else if (tk == GCD_F)
				r = poly_gcd(coef_t, coef_a);
			else
				r = poly_quotient(coef_t, coef_a, tk);
			coef_t = clear_map(coef_t); coef_a = clear_map(coef_a);
			Tree* ret = polyreconstitute(&r, ((Tree*)L->end->data)->value);
			L = clear_map(L);
			return pow_transform(ret);
		}
		L = clear_map(L);
		Error = push_back_dlist(Error, err_msg[0]);
		return NULL;
	}
	ALG_EXPAND = true;
	return Contract_pow(simplify(tr));
}

Tree* analyse(Tree* tr)
{
	return pow_transform(analyse_rules(tr));
}