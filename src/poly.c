#include "includes.h"

bool ismonomial(Tree* u, const char* x)
{
	if (u->tok_type == POW)
		return ismonomial(u->tleft, x) && u->tright->gtype == ENT;
	if (u->tok_type == PROD)
		return ismonomial(u->tleft, x) && ismonomial(u->tright, x);
	if (u->tok_type == DIVID)
		return ismonomial(u->tleft, x) && !ismonomial(u->tright, x);
	if (u->tok_type == NEGATIF)
		return ismonomial(u->tleft, x);
	return (!strcmp(u->value, x) || !found_element(u, x));
}

static Tree* degree_monomial_sv(Tree* u, const char* x)
{
	if (!strcmp(u->value, "0"))
		return join(new_tree("1"), NULL, fnc[NEGATIF].ex);
	else if (isconstant(u))
		return new_tree("0");
	else if (!strcmp(u->value, x))
		return new_tree("1");
	else if (u->tok_type == POW && !strcmp(u->tleft->value, x) && u->tright->gtype == ENT && Eval(u->tright) >= 1)
		return clone(u->tright);
	else if (u->tok_type == NEGATIF || u->tok_type == DIVID)
		return degree_monomial_sv(u->tleft, x);
	else if (u->tok_type == PROD)
	{
		Tree* s = degree_monomial_sv(u->tleft, x), * t = degree_monomial_sv(u->tright, x);
		if (strcmp(s->value, fnc[UNDEF].ex) && strcmp(t->value, fnc[UNDEF].ex))
		{
			clean_tree(s);
			return t;
		}
		clean_tree(s);
		clean_tree(t);
	}
	return new_tree(fnc[UNDEF].ex);
}

Tree* degree_sv(Tree* u, const char* x)
{
	Tree* d = degree_monomial_sv(u, x);
	if (strcmp(d->value, fnc[UNDEF].ex))
		return d;
	clean_tree(d);
	if (u->tok_type == ADD || u->tok_type == SUB)
	{
		map L = map_create_add(u);
		Cell* tmp = L->begin;
		d = new_tree("0");
		while (tmp != NULL)
		{
			Tree* f = degree_monomial_sv(tmp->data, x);
			if (!strcmp(f->value, fnc[UNDEF].ex))
			{
				clean_tree(d);
				L = clear_map(L);
				return f;
			}
			else if (Eval(d) < Eval(f))
			{
				clean_tree(d);
				d = clone(f);
			}
			clean_tree(f);
			tmp = tmp->next;
		}
		L = clear_map(L);
		return d;
	}
	else if (u->tok_type == DIVID)
		return degree_sv(u->tleft, x);
	else if (u->tok_type == PROD && isconstant(u->tleft))
		return degree_sv(u->tright, x);
	return new_tree(fnc[UNDEF].ex);
}

Tree* coefficient_gpe(Tree* u, const char* x, unsigned j)
{
	map cf = polycoeffs(u, x);
	unsigned i = cf->length - 1;
	for (Cell* tmp = cf->begin; tmp != NULL; tmp = tmp->next)
	{
		if (i == j)
		{
			Tree* a = clone(tmp->data);
			cf = clear_map(cf);
			return a;
		}
		i--;
	}
	cf = clear_map(cf);
	return new_tree("0");
}

Tree* polyreconstitute(map* Li, const char* x)
{
	int n = (*Li)->length;
	Tree* u = NULL;
	for (Cell* tmp = (*Li)->begin; tmp != NULL; tmp = tmp->next)
	{
		if (strcmp(((Tree*)tmp->data)->value, "0"))
		{
			Tree* v = clone(tmp->data);
			if (n > 2)
				v = join(v, join(new_tree(x), new_tree(tostr(n - 1)), fnc[POW].ex), fnc[PROD].ex);
			else if (n == 2)
				v = join(v, new_tree(x), fnc[PROD].ex);
			u = (u == NULL) ? v : join(v, u, fnc[ADD].ex);
		}
		n--;
	}
	(*Li) = clear_map(*Li);
	return u;
}

static bool iszero(map Li)
{
	for (Cell* celdivd = Li->begin; celdivd != NULL; celdivd = celdivd->next)
		if (strcmp(((Tree*)celdivd->data)->value, "0"))
			return false;
	return true;
}

static map remain(map divr, map divd, Tree* a)
{
	for (Cell* t = divr->begin, * celdivd = divd->begin; t != NULL; t = t->next, celdivd = celdivd->next)
	{
		Tree* s = join(clone(a), clone(t->data), fnc[PROD].ex);
		celdivd->data = simplify(join(celdivd->data, s, fnc[SUB].ex));
	}
	return divd;
}

map polynomial_division(map* divd, map* divr, map* rem)
{
	map quot = NULL;
	Tree* a = NULL;
	if ((*divd)->length < (*divr)->length)
		return polynomial_division(divr, divd, rem);
	while ((*divd)->length >= (*divr)->length)
	{
		a = simplify(join(clone((*divd)->begin->data), clone((*divr)->begin->data), fnc[DIVID].ex));
		*divd = remain(*divr, *divd, a);
		quot = push_back(quot, a);
		(*divd) = pop_front_map(*divd);
		if ((*divd) == NULL)
			break;
		if (iszero(*divd))
		{
			for (int i = 1; i < (*divd)->length - (*divr)->length; ++i)
				quot = push_back(quot, new_tree("0"));
			(*divd) = clear_map(*divd);
			break;
		}
	}
	if ((*divd) == NULL)
		(*divd) = push_back(*divd, new_tree("0"));
	(*divr) = clear_map(*divr);
	*rem = (*divd);
	return quot;
}

map poly_quotient(map u, map v, token tk)
{
	map rem = NULL, coef_u = clone_map(u), coef_v = clone_map(v);
	map L = polynomial_division(&coef_u, &coef_v, &rem);
	if (tk == REMAINDER_F)
	{
		L = clear_map(L);
		return rem;
	}
	rem = clear_map(rem);
	return L;
}

map poly_gcd(map u, map v)
{
	if (u->length == 1 && !strcmp(((Tree*)u->begin->data)->value, "0") && v->length == 1 && !strcmp(((Tree*)v->begin->data)->value, "0"))
		return push_back(NULL, new_tree("1"));
	if (v->length == 1 && u->length == 1)
		return push_back(NULL, PGCD(clone(u->begin->data), clone(v->begin->data)));
	bool k = v->length > u->length;
	map U = k ? clone_map(v) : clone_map(u);
	map V = k ? clone_map(u) : clone_map(v);
	while (strcmp(((Tree*)V->begin->data)->value, "0"))
	{
		map R = poly_quotient(U, V, REMAINDER_F);
		U = clear_map(U);
		U = V;
		V = R;
	}
	V = clear_map(V);
	if (U->length > 1)
	{
		Tree* lcr = clone(U->begin->data);
		for (Cell* tmp = U->begin; tmp != NULL; tmp = tmp->next)
			tmp->data = simplify(join(tmp->data, clone(lcr), fnc[DIVID].ex));
		clean_tree(lcr);
	}
	return U;
}

Tree* poly_simp(map u, map v, const char* x)
{
	map pgcd = poly_gcd(u, v);
	if (pgcd->length > 1 || (pgcd->length == 1 && strcmp(((Tree*)pgcd->begin->data)->value, "1")))
	{
		map qn = poly_quotient(u, pgcd, INT_F), qd = poly_quotient(v, pgcd, INT_F);
		pgcd = clear_map(pgcd); u = clear_map(u); v = clear_map(v);
		Tree* n = polyreconstitute(&qn, x), * d = polyreconstitute(&qd, x);
		if (!strcmp(d->value, "1"))
		{
			clean_tree(d);
			return n;
		}
		return join(n, d, fnc[DIVID].ex);
	}
	pgcd = clear_map(pgcd);
	return join(polyreconstitute(&u, x), polyreconstitute(&v, x), fnc[DIVID].ex);
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
		char* fi = factoriel(i);
		r = simplify(join(remplace_tree(d, x, z), new_tree(fi), fnc[DIVID].ex));
		free(fi);
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

static Tree* roots(map coefs, int* n, int i, int* d, int j)
{
	int* l = malloc(coefs->length * sizeof(int)), k = 0;
	Cell* tmp = coefs->begin;
	while (tmp != NULL)
	{
		l[k++] = Eval(tmp->data);
		tmp = tmp->next;
	}
	for (int a = 0; a < i; a++)
	{
		double r = 0.0, s = 0.0;
		for (int b = 0; b < j; b++)
		{
			int p = coefs->length - 1;
			for (int c = 0; c < coefs->length; c++)
			{
				r += (double)(l[c] * pow((double)(n[a] / d[b]), p));
				s += (double)(l[c] * pow((double)(-n[a] / d[b]), p));
				p--;
			}
			if (fabs(r) <= 0.0001 || fabs(s) <= 0.0001)
			{
				Tree* sol = simplify(join(new_tree(tostr(n[a])), new_tree(tostr(d[b])), fnc[DIVID].ex));
				free(n); free(d); free(l);
				if (r == 0)
					sol = join(sol, NULL, fnc[NEGATIF].ex);
				return sol;
			}
		}
	}
	free(n); free(d); free(l);
	return  NULL;
}

static int* factor_list(int n, int* len)
{
	int* l = malloc(n * sizeof(int)), pos = 0;
	for (int i = 1; i <= n; i++)
		if (!(n % i))
			l[pos++] = i;
	*len = pos;
	return l;
}

Tree* pfactor(map coefs, const char* x)
{
	if (coefs->length > 2)
	{
		int n = abs((int)Eval(coefs->end->data)), d = abs((int)Eval(coefs->begin->data)), i = 0, j = 0;
		int* list_n = factor_list(n, &i), * list_d = factor_list(d, &j);
		Tree* s = roots(coefs, list_n, i, list_d, j);
		if (s != NULL)
		{
			Tree* denom_s = denominator_fun(s);
			map S = push_back(NULL, new_tree("1"));
			if (!strcmp(denom_s->value, "1"))
			{
				clean_tree(denom_s);
				S = push_back(S, s);
				denom_s = NULL;
			}
			else
			{
				S = push_back(S, numerator_fun(s));
				clean_tree(s);
			}
			j = 0;
			map rem = NULL, quot = NULL;
			map cS = clone_map(S);
			map quo = polynomial_division(&coefs, &cS, &rem);
			while (rem->length == 1 && !strcmp(((Tree*)rem->begin->data)->value, "0") && strcmp(((Tree*)quo->begin->data)->value, "0"))
			{
				rem = clear_map(rem);
				cS = clone_map(S);
				if (quot != NULL)
					quot = clear_map(quot);
				quot = clone_map(quo);
				map n_quo = polynomial_division(&quo, &cS, &rem);
				quo = n_quo;
				j++;
			}
			quo = clear_map(quo);
			rem = clear_map(rem);
			Tree* w = pfactor(quot, x), * v = polyreconstitute(&S, x);
			if (j > 1)
				v = join(v, new_tree(tostr(j)), fnc[POW].ex);
			if (denom_s != NULL)
				v = join(denom_s, v, fnc[PROD].ex);
			if (!strcmp(w->value, "0"))
			{
				clean_tree(w);
				return v;
			}
			return join(v, w, fnc[PROD].ex);
		}
	}
	return polyreconstitute(&coefs, x);
}