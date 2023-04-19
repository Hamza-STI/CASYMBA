#include "calculs.h"

DList Error = NULL;

static Tree* factor_by_int(Tree* u, const char* x)
{
	for (unsigned i = 1; i <= 10; i++)
	{
		Tree* v = new_tree(tostr(i)), * w = join(new_tree(tostr(i)), NULL, fnc[NEGATIF].ex);
		Tree* r = simplify(remplace_tree(u, x, v)), * s = simplify(remplace_tree(u, x, w));
		if (!strcmp(r->value, "0") || !strcmp(s->value, "0"))
		{
			map cf = polycoeffs(u, x), R = NULL;
			Tree* un = new_tree("1");
			R = push_back_map(push_back_map(R, un), (!strcmp(s->value, "0")) ? v : w);
			clean_tree(r); clean_tree(s); clean_tree(v); clean_tree(w); clean_tree(un);
			map Q = poly_quotient(cf, R);
			Tree* q = polyreconstitute(&Q, x), * f = polyreconstitute(&R, x);
			r = square_free_factor(q, x);
			cf = clear_map(cf);
			clean_tree(q);
			return join(f, r, fnc[PROD].ex);
		}
		clean_tree(r); clean_tree(s); clean_tree(v); clean_tree(w);
	}
	return  clone(u);
}

Tree* square_free_factor(Tree* u, const char* x)
{
	map cf = polycoeffs(u, x), coef_u = NULL, coef_v = NULL;
	Tree* c = clone(cf->begin->tr);
	mapCell* tmp = cf->begin;
	while (tmp != NULL)
	{
		Tree* q = simplify(join(clone(tmp->tr), clone(c), fnc[DIVID].ex));
		coef_u = push_back_map(coef_u, q);
		clean_tree(q);
		tmp = tmp->next;
	}
	cf = clear_map(cf);
	int k = coef_u->length;
	int i = k - 1;
	tmp = coef_u->begin;
	while (i > 0)
	{
		Tree* q = simplify(join(clone(tmp->tr), new_tree(tostr(i)), fnc[PROD].ex));
		coef_v = push_back_map(coef_v, q);
		clean_tree(q);
		i--;
		tmp = tmp->next;
	}
	map R = poly_gcd(coef_u, coef_v);
	coef_v = clear_map(coef_v);
	map F = poly_quotient(coef_u, R);
	coef_u = clear_map(coef_u);
	if (R->length == 1 && !strcmp(R->begin->tr->value, "1") && k > 2)
	{
		R = clear_map(R); F = clear_map(F);
		clean_tree(c);
		return factor_by_int(u, x);
	}
	Tree* P = NULL;
	int j = 1;
	while (R->length > 1 || (R->length == 1 && strcmp(R->begin->tr->value, "1")))
	{
		map G = poly_gcd(R, F);
		map q = poly_quotient(F, G);
		Tree* s = polyreconstitute(&q, x);
		if (j > 1 && strcmp(s->value, "1"))
			s = join(s, new_tree(tostr(j)), fnc[POW].ex);
		if (strcmp(s->value, "1"))
			P = (P == NULL) ? s : join(P, s, fnc[PROD].ex);
		else
			clean_tree(s);
		map tmp = poly_quotient(R, G);
		R = clear_map(R); F = clear_map(F);
		R = tmp;
		F = G;
		j++;
	}
	R = clear_map(R);
	Tree* f = polyreconstitute(&F, x);
	if (j > 1)
		f = join(f, new_tree(tostr(j)), fnc[POW].ex);
	P = (P == NULL) ? f : join(P, f, fnc[PROD].ex);
	if (!strcmp(c->value, "1"))
	{
		clean_tree(c);
		return P;
	}
	return join(c, P, fnc[PROD].ex);
}

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
	Tree* dtrc = remplace_tree(dtr, vr, point), * trc = remplace_tree(clone(tr), vr, point);
	Tree* tantr = join(join(dtrc, join(new_tree(vr), clone(point), fnc[SUB].ex), fnc[PROD].ex), trc, fnc[ADD].ex);
	return simplify(tantr);
}

/* développements limités : Taylor */

static Tree* taylor_usuelle(Tree* u, const char* vr, Tree* ordre, Tree* point)
{
	Tree* s = simplify(remplace_tree(u, vr, point));
	if (s->tok_type == UNDEF)
	{
		clean_tree(s);
		Error = push_back_dlist(Error, "Non géré.");
		return NULL;
	}
	Tree* dtr = clone(u);
	int n = (int)tonumber(ordre->value), i;
	for (i = 1; i <= n; i++)
	{
		Tree* diff_r = simplify(diff(dtr, vr));
		clean_tree(dtr);
		dtr = diff_r;
		Tree* a = join(simplify(remplace_tree(dtr, vr, point)), new_tree(tostr(factoriel(i))), fnc[DIVID].ex);
		Tree* b = join(simplify(join(new_tree(vr), clone(point), fnc[SUB].ex)), new_tree(tostr(i)), fnc[POW].ex);
		Tree* c = simplify(join(a, b, fnc[PROD].ex));
		if (c->tok_type == UNDEF)
		{
			clean_tree(c); clean_tree(s); clean_tree(dtr);
			Error = push_back_dlist(Error, "Non géré. No solution.");
			return NULL; // erreur
		}
		if (strcmp(c->value, "0"))
			s = (s == NULL)? c : join(s, c, fnc[ADD].ex);
		else
			clean_tree(c);
	}
	clean_tree(dtr);
	return s;
}

static bool usuelle_forme(token a)
{
	return a == COS_F || a == SIN_F || a == LN_F || a == COSH_F || a == SINH_F || a == EXP_F;
}

static Tree* taylor(Tree* u, Tree* vr, Tree* ordre, Tree* point)
{
	if ((u->tok_type == LN_F || u->tok_type == SQRT_F || u->tok_type == POW) && ismonomial(u->tleft, vr->value))
		return clone(u);
	if (usuelle_forme(u->tok_type))
	{
		if (u->tleft->tok_type == SQRT_F)
		{
			Tree* z = new_tree("0");
			Tree* R = simplify(substitute(u->tleft->tleft, vr, z));
			bool k = !strcmp(R->value, "0");
			clean_tree(z); clean_tree(R);
			if (k)
			{
				z = new_tree("B");
				R = join(z, NULL, u->value);
				Tree* s = taylor_usuelle(R, z->value, ordre, point);
				clean_tree(R);
				R = substitute(s, z, u->tleft);
				clean_tree(s);
				return simplify(R);
			}
		}
		else
			return taylor_usuelle(u, vr->value, ordre, point);
	}
	else if (u->tok_type == SQRT_F || u->tok_type == POW)
		return taylor_usuelle(u, vr->value, ordre, point);
	else if (u->tok_type == PROD)
	{
		Tree* v = taylor(u->tleft, vr, ordre, point), * w = taylor(u->tright, vr, ordre, point);
		if (v == NULL || w == NULL)
		{
			Error = push_back_dlist(Error, "Non géré.");
			return NULL;
		}
		map lv = map_create_add(v), lw = map_create_add(w);
		Tree* d = NULL, * s = new_tree("0");
		mapCell* tmp_v = lv->begin, * tmp_w = NULL;
		double g = Eval(ordre), h = 0;
		while (tmp_v != NULL)
		{
			tmp_w = lw->begin;
			while (tmp_w != NULL)
			{
				d = join(degree_sv(tmp_v->tr, vr->value), degree_sv(tmp_w->tr, vr->value), fnc[ADD].ex);
				h = Eval(d);
				clean_tree(d);
				if (h <= g)
					s = join(s, simplify(join(tmp_v->tr, tmp_w->tr, fnc[PROD].ex)), fnc[ADD].ex);
				else
					break;
				tmp_w = tmp_w->next;
			}
			tmp_v = tmp_v->next;
		}
		lv = clear_map(lv);
		lw = clear_map(lw);
		clean_tree(v); clean_tree(w);
		return simplify(s);
	}
	else if (u->tok_type == ADD || u->tok_type == SUB)
	{
		Tree* v = taylor(u->tleft, vr, ordre, point), * w = taylor(u->tright, vr, ordre, point);
		if (v == NULL || w == NULL)
		{
			if (v != NULL)
				clean_tree(v);
			if (w != NULL)
				clean_tree(w);
			Error = push_back_dlist(Error, "Non géré.");
			return NULL;
		}
		return simplify(join(v, w, u->value));
	}
	return clone(u);
}

/* équations differentielles linéaires */

static Tree* trig_separe(Tree* f, const char* x, Tree** part)
{
	map M = map_create_prod(f);
	Tree* part_trig = NULL;
	mapCell* tmp = M->begin;
	while (tmp != NULL)
	{
		if ((tmp->tr->tok_type == SIN_F || tmp->tr->tok_type == COS_F) && found_element(tmp->tr, x))
			part_trig = clone(tmp->tr);
		else
			*part = (*part == NULL) ? clone(tmp->tr) : join(*part, clone(tmp->tr), fnc[PROD].ex);
		tmp = tmp->next;
	}
	if (*part == NULL)
		*part = new_tree("1");
	M = clear_map(M);
	return part_trig;
}

static map homogenious_2(Tree* a, Tree* b, Tree* c, const char* x, map* S)
{
	map L = NULL;
	if (!strcmp(a->value, "1") && !strcmp(b->value, "0"))
	{
		Tree* d = simplify(join(clone(c), NULL, fnc[SQRT_F].ex));
		Tree* cs = join(join(clone(d), new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex);
		Tree* sn = join(join(clone(d), new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex);
		*S = push_back_map(*S, d);
		L = push_back_map(push_back_map(L, cs), sn);
		clean_tree(cs);
		clean_tree(sn);
		clean_tree(d);
		return L;
	}
	Tree* D = simplify(join(clone((b->tok_type == NEGATIF)? b->tleft : b), new_tree("2"), fnc[POW].ex));
	Tree* e = simplify(join(join(new_tree("4"), clone(a), fnc[PROD].ex), clone(c), fnc[PROD].ex));
	D = simplify(join(D, e, fnc[SUB].ex));
	double d = Eval(D);
	if (d > 0)
	{
		e = (b->tok_type == NEGATIF)? clone(b->tleft) : join(clone(b), NULL, fnc[NEGATIF].ex);
		Tree* P = simplify(e), * O = simplify(join(D, NULL, fnc[SQRT_F].ex));
		Tree* Z = simplify(join(new_tree("2"), clone(a), fnc[PROD].ex));
		Tree* r1 = simplify(join(join(clone(P), clone(O), fnc[ADD].ex), clone(Z), fnc[DIVID].ex));
		Tree* r2 = simplify(join(join(P, O, fnc[SUB].ex), Z, fnc[DIVID].ex));
		*S = push_back_map(push_back_map(*S, r1), r2);
		Tree* y1 = join(join(r1, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* y2 = join(join(r2, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		L = push_back_map(push_back_map(L, y1), y2);
		clean_tree(y1);
		clean_tree(y2);
	}
	else if (d == 0)
	{
		Tree* com = simplify(join(clone(b), join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex));
		com = simplify(join(com, NULL, fnc[NEGATIF].ex));
		*S = push_back_map(*S, com);
		com = join(join(com, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* y = join(clone(com), new_tree(x), fnc[PROD].ex);
		L = push_back_map(push_back_map(L, com), y);
		clean_tree(com);
		clean_tree(y);
		clean_tree(D);
	}
	else if (d < 0)
	{
		e = (b->tok_type == NEGATIF)? clone(b->tleft) : join(clone(b), NULL, fnc[NEGATIF].ex);
		Tree* com = join(e, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex);
		com = simplify(com);
		*S = push_back_map(*S, com);
		com = join(join(com, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* r = join(join(D, NULL, fnc[NEGATIF].ex), NULL, fnc[SQRT_F].ex);
		r = simplify(join(r, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex));
		*S = push_back_map(*S, r);
		Tree* y1 = join(clone(com), join(join(clone(r), new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
		Tree* y2 = join(com, join(join(r, new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex), fnc[PROD].ex);
		L = push_back_map(push_back_map(L, y1), y2);
		clean_tree(y1);
		clean_tree(y2);
	}
	return L;
}

static Tree* system_rmp(Tree* tr, DList v, map L)
{
	DListCell* tmp = v->begin;
	mapCell* tmp_L = L->begin;
	while (tmp != NULL)
	{
		tr = remplace_var(tr, tmp->value, tmp_L->tr);
		tmp_L = tmp_L->next;
		tmp = tmp->next;
	}
	return tr;
}

static map solve_system(map* L, map* R)
{
	mapCell* tmp_L = (*L)->begin, * tmp_R = (*R)->begin;
	DList vrs = NULL, v_ps = NULL;
	map rt = NULL;
	Tree* z = new_tree("0"), * o = new_tree("1");
	while (tmp_L != NULL)
	{
		Tree* t = clone(tmp_L->tr);
		if (v_ps != NULL)
			t = system_rmp(t, v_ps, rt);
		vrs = getvars(t, vrs);
		if (vrs != NULL && vrs->length == 1)
		{
			Tree* a = coefficient_gpe(t, vrs->end->value, o), * b = coefficient_gpe(t, vrs->end->value, z);
			Tree* q = simplify(join(clone(tmp_R->tr), b, fnc[SUB].ex));
			q = simplify(join(q, a, fnc[DIVID].ex));
			v_ps = push_back_dlist(v_ps, vrs->end->value);
			rt = push_back_map(rt, q);
			clean_tree(q);
		}
		else if (vrs == NULL)
			rt = push_back_map(rt, t);
		vrs = clear_dlist(vrs);
		clean_tree(t);
		tmp_L = tmp_L->next;
		tmp_R = tmp_R->next;
	}
	v_ps = clear_dlist(v_ps);
	*L = clear_map(*L); *R = clear_map(*R);
	clean_tree(z); clean_tree(o);
	return rt;
}

static Tree* create_poly(const char* cf, int i, Tree* dg, const char* x)
{
	if (i > 1)
		return join(new_tree(cf), join(new_tree(x), clone(dg), fnc[POW].ex), fnc[PROD].ex);
	if (i == 1)
		return join(new_tree(cf), new_tree(x), fnc[PROD].ex);
	return new_tree(cf);
}

static Tree* poly_solution_2(Tree* a, Tree* b, Tree* c, Tree* part, const char* x, Tree* dg)
{
	Tree* Pl = NULL, * d = clone(dg), * z = new_tree("0");
	int w = (int)tonumber(dg->value);
	map cf = NULL, cpl = NULL, sol = NULL;
	DList vr = NULL;
	mapCell* tmp = NULL;
	DListCell* cel_vr = NULL;
	for (int i = w; i >= 0; i--)
		cpl = push_back_map(cpl, z);
	clean_tree(z);
	for (int i = w; i >= 0; i--)
	{
		char ct[] = { 'M', '0' + i, '\0' };
		Tree* cf_i = coefficient_gpe(part, x, dg);
		vr = push_back_dlist(vr, ct);
		cf = push_front_map(cf, cf_i);
		clean_tree(cf_i);
		z = create_poly(ct, i, dg, x);
		Pl = (Pl == NULL) ? z : join(Pl, z, fnc[ADD].ex);
		if (strcmp(c->value, "0"))
			cpl = map_remplace(cpl, i, join(clone(c), new_tree(ct), fnc[PROD].ex));
		if (i - 1 >= 0 && strcmp(b->value, "0"))
			cpl = map_remplace(cpl, i - 1, join(join(new_tree(tostr(i)), clone(b), fnc[PROD].ex), new_tree(ct), fnc[PROD].ex));
		if (i - 2 >= 0 && strcmp(a->value, "0"))
			cpl = map_remplace(cpl, i - 2, join(join(new_tree(tostr(i * (i - 1))), clone(a), fnc[PROD].ex), new_tree(ct), fnc[PROD].ex));
		dg = simplify(join(dg, new_tree("1"), fnc[SUB].ex));
	}
	clean_tree(dg); clean_tree(a); clean_tree(b); clean_tree(c); clean_tree(d); clean_tree(part);
	sol = solve_system(&cpl, &cf);
	tmp = sol->begin;
	cel_vr = vr->begin;
	while (tmp != NULL)
	{
		Pl = remplace_var(Pl, cel_vr->value, tmp->tr);
		tmp = tmp->next;
		cel_vr = cel_vr->next;
	}
	vr = clear_dlist(vr);
	sol = clear_map(sol);
	return simplify(Pl);
}

static Tree* exp_solution_2(Tree* a, Tree* b, Tree* c, const char* x, Tree* dg, Tree* part, Tree* part_exp, Tree* r)
{
	Tree* u = NULL, * v = NULL, * Pl = NULL;
	if (!strcmp(a->value, "0"))
	{
		u = b;
		v = simplify(join(join(clone(b), r, fnc[PROD].ex), c, fnc[ADD].ex));
	}
	else
	{
		u = simplify(join(join(join(new_tree("2"), clone(a), fnc[PROD].ex), clone(r), fnc[PROD].ex), clone(b), fnc[ADD].ex));
		v = simplify(join(join(join(clone(a), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), join(b, r, fnc[PROD].ex), fnc[ADD].ex), c, fnc[ADD].ex));
	}
	Pl = poly_solution_2(a, u, v, part, x, dg);
	return join(Pl, part_exp, fnc[PROD].ex);
}

static Tree* trig_solution_2(Tree* a, Tree* b, Tree* c, const char* x, Tree* dg, Tree* part, Tree* part1, Tree* trig, Tree* trig1)
{
	if (!strcmp(dg->value, "0"))
	{
		Tree* m1 = NULL, * denom = NULL, * m2 = NULL;
		Tree* o = new_tree("1");
		Tree* r = coefficient_gpe(trig->tleft, x, o);
		clean_tree(o); clean_tree(dg);
		m1 = join(join(join(clone(a), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(c), fnc[SUB].ex), clone(part), fnc[PROD].ex);
		m1 = join(m1, join(join(clone(b), clone(r), fnc[PROD].ex), clone(part1), fnc[PROD].ex), fnc[ADD].ex);
		m1 = simplify(join(m1, NULL, fnc[NEGATIF].ex));
		m2 = join(join(join(clone(a), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(c), fnc[SUB].ex), part1, fnc[PROD].ex);
		m2 = join(m2, join(join(clone(b), clone(r), fnc[PROD].ex), part, fnc[PROD].ex), fnc[ADD].ex);
		m2 = simplify(join(m2, NULL, fnc[NEGATIF].ex));
		denom = join(join(clone(a), new_tree("2"), fnc[POW].ex), join(clone(r), new_tree("4"), fnc[POW].ex), fnc[PROD].ex);
		denom = join(denom, join(join(join(new_tree("2"), a, fnc[PROD].ex), c, fnc[PROD].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[SUB].ex);
		denom = join(denom, join(join(b, new_tree("2"), fnc[POW].ex), join(r, new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[ADD].ex);
		denom = simplify(join(denom, join(clone(c), new_tree("2"), fnc[POW].ex), fnc[ADD].ex));
		m1 = simplify(join(m1, clone(denom), fnc[DIVID].ex));
		m2 = simplify(join(m2, denom, fnc[DIVID].ex));
		return join(join(m1, trig, fnc[PROD].ex), join(m2, trig1, fnc[PROD].ex), fnc[ADD].ex);
	}
	else if (!strcmp(dg->value, "1"))
	{
		Tree* m1 = NULL, * m2 = NULL, * m3 = NULL, * m4 = NULL, * denom = NULL;
		Tree* z = new_tree("0");
		Tree* r = coefficient_gpe(trig->tleft, x, dg);
		Tree* c_x1 = coefficient_gpe(part, x, dg), * c_x0 = coefficient_gpe(part, x, z);
		Tree* s_x1 = coefficient_gpe(part1, x, dg), * s_x0 = coefficient_gpe(part1, x, z);
		clean_tree(z); clean_tree(dg); clean_tree(part); clean_tree(part1);
		m1 = join(join(join(clone(a), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(c), fnc[SUB].ex), clone(c_x1), fnc[PROD].ex);
		m1 = join(m1, join(join(clone(b), clone(r), fnc[PROD].ex), clone(s_x1), fnc[PROD].ex), fnc[ADD].ex);
		m1 = simplify(join(m1, NULL, fnc[NEGATIF].ex));
		m3 = join(join(join(clone(a), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(c), fnc[SUB].ex), s_x1, fnc[PROD].ex);
		m3 = join(m3, join(join(clone(b), clone(r), fnc[PROD].ex), c_x1, fnc[PROD].ex), fnc[ADD].ex);
		m3 = simplify(join(m3, NULL, fnc[NEGATIF].ex));
		denom = join(join(clone(a), new_tree("2"), fnc[POW].ex), join(clone(r), new_tree("4"), fnc[POW].ex), fnc[PROD].ex);
		denom = join(denom, join(join(join(new_tree("2"), clone(a), fnc[PROD].ex), clone(c), fnc[PROD].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[SUB].ex);
		denom = join(denom, join(join(clone(b), new_tree("2"), fnc[POW].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[ADD].ex);
		denom = simplify(join(denom, join(clone(c), new_tree("2"), fnc[POW].ex), fnc[ADD].ex));
		m1 = simplify(join(m1, clone(denom), fnc[DIVID].ex));
		m3 = simplify(join(m3, clone(denom), fnc[DIVID].ex));

		m2 = join(join(join(new_tree("2"), join(clone(a), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), join(clone(r), new_tree("3"), fnc[POW].ex), fnc[PROD].ex), clone(m3), fnc[PROD].ex);
		m2 = join(m2, join(join(join(clone(a), clone(b), fnc[PROD].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(m1), fnc[PROD].ex), fnc[SUB].ex);
		m2 = join(m2, join(join(join(join(new_tree("2"), clone(a), fnc[PROD].ex), clone(c), fnc[PROD].ex), clone(r), fnc[PROD].ex), clone(m3), fnc[PROD].ex), fnc[SUB].ex);
		m2 = join(m2, join(join(clone(a), clone(c_x0), fnc[PROD].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[ADD].ex);
		m2 = join(m2, join(join(clone(r), join(clone(b), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(m3), fnc[PROD].ex), fnc[ADD].ex);
		m2 = join(m2, join(clone(b), join(clone(c), clone(m1), fnc[PROD].ex), fnc[PROD].ex), fnc[SUB].ex);
		m2 = join(m2, join(clone(b), join(clone(r), clone(s_x0), fnc[PROD].ex), fnc[PROD].ex), fnc[SUB].ex);
		m2 = join(m2, join(clone(c), clone(c_x0), fnc[PROD].ex), fnc[ADD].ex);
		m2 = simplify(join(m2, clone(denom), fnc[DIVID].ex));

		m4 = join(join(join(join(new_tree("2"), NULL, fnc[NEGATIF].ex), join(clone(a), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), join(clone(r), new_tree("3"), fnc[POW].ex), fnc[PROD].ex), clone(m1), fnc[PROD].ex);
		m4 = join(m4, join(join(join(clone(a), clone(b), fnc[PROD].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(m3), fnc[PROD].ex), fnc[SUB].ex);
		m4 = join(m4, join(join(join(join(new_tree("2"), clone(a), fnc[PROD].ex), clone(c), fnc[PROD].ex), clone(r), fnc[PROD].ex), clone(m1), fnc[PROD].ex), fnc[ADD].ex);
		m4 = join(m4, join(join(a, s_x0, fnc[PROD].ex), join(clone(r), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[SUB].ex);
		m4 = join(m4, join(join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), clone(m1), fnc[PROD].ex), fnc[SUB].ex);
		m4 = join(m4, join(clone(b), join(clone(c), clone(m3), fnc[PROD].ex), fnc[PROD].ex), fnc[SUB].ex);
		m4 = join(m4, join(b, join(clone(r), c_x0, fnc[PROD].ex), fnc[PROD].ex), fnc[ADD].ex);
		m4 = join(m4, join(c, clone(s_x0), fnc[PROD].ex), fnc[ADD].ex);
		m4 = simplify(join(m4, denom, fnc[DIVID].ex));
		m1 = join(join(m1, new_tree(x), fnc[PROD].ex), m2, fnc[ADD].ex);
		m3 = join(join(m3, new_tree(x), fnc[PROD].ex), m4, fnc[ADD].ex);
		return join(join(m1, trig, fnc[PROD].ex), join(m3, trig1, fnc[PROD].ex), fnc[ADD].ex);
	}
	Error = push_back_dlist(Error, "Non géré. No solution.");
    clean_tree(dg);
	return NULL; // erreur cas non géré
}

static Tree* solve_exact_2(Tree* a, Tree* b, Tree* c, Tree* f, map S, const char* x)
{
	if (!found_element(f, x))
	{
		Tree* q = simplify(join(f, c, fnc[DIVID].ex));
		clean_tree(a); clean_tree(b);
		return q;
	}
	if (ispoly(f, x))
	{
		Tree* dg = degree_sv(f, x);
		return poly_solution_2(a, b, c, f, x, dg);
	}
	else
	{
		int e = found_element(f, fnc[EXP_F].ex), cs = found_element(f, fnc[COS_F].ex);
		int sn = found_element(f, fnc[SIN_F].ex);
		if (e && !cs && !sn)
		{
			map M = map_create_prod(f);
			Tree* part_exp = NULL, * part = NULL;
			mapCell* tmp = M->begin;
			clean_tree(f);
			while (tmp != NULL)
			{
				if (tmp->tr->tok_type == EXP_F && found_element(tmp->tr, x))
					part_exp = clone(tmp->tr);
				else
					part = (part == NULL) ? clone(tmp->tr) : join(part, clone(tmp->tr), fnc[PROD].ex);
				tmp = tmp->next;
			}
			if (part == NULL)
				part = new_tree("1");
			M = clear_map(M);
			tmp = S->begin;
			Tree* o = new_tree("1");
			Tree* r = coefficient_gpe(part_exp->tleft, x, o), * dg = degree_sv(part, x);
			clean_tree(o);
			while (tmp != NULL)
			{
				if (tree_compare(r, tmp->tr))
				{
					dg = simplify(join(dg, new_tree((strcmp(a->value, "0") && S->length == 1) ? "2" : "1"), fnc[ADD].ex));
					break;
				}
				tmp = tmp->next;
			}
			return exp_solution_2(a, b, c, x, dg, part, part_exp, r);
		}
		else if ((sn || cs) && !e)
		{
			Tree* trig = NULL, * part = NULL, * part1 = NULL, * trig1 = NULL;
			if (f->tok_type == PROD && (f->tleft->tok_type == ADD || f->tleft->tok_type == SUB || f->tright->tok_type == ADD || f->tright->tok_type == SUB))
			{
				TRIG_EXPAND = false;
				Tree* F = expand(f), * p = f->parent;
				clean_tree(f);
				f = simplify(F);
				f->parent = p;
			}
			if (f->tok_type == ADD || f->tok_type == SUB)
			{
				map R = map_create_add(f);
				clean_tree(f);
				if (R->length != 2)
				{
					R = clear_map(R);
					Error = push_back_dlist(Error, "Error : excepted form Acos(U)+Bsin(U).");
					return NULL; //retourner une erreur forme attendu Acos(U)+Bsin(U)
				}
				trig = trig_separe(R->begin->tr, x, &part);
				trig1 = trig_separe(R->end->tr, x, &part1);
				R = clear_map(R);
				if (trig == NULL || trig1 == NULL || trig->tok_type == trig1->tok_type || !tree_compare(trig->tleft, trig1->tleft))
				{
					clean_tree(trig); clean_tree(trig1); clean_tree(part1); clean_tree(part);
					Error = push_back_dlist(Error, "Error : excepted form Acos(U)+Bsin(U).");
					return NULL; //retourner une erreur forme attendu Acos(U)+Bsin(U)
				}
			}
			else
			{
				trig = trig_separe(f, x, &part);
				clean_tree(f);
				part1 = new_tree("0");
			}
			Tree* ng = new_tree("1");
			Tree* nx = coefficient_gpe(trig->tleft, x, ng), * dg = degree_sv(part, x);
			if (tree_compare(nx, S->end->tr))
				dg = simplify(join(dg, new_tree("1"), fnc[ADD].ex));
			clean_tree(ng);
			clean_tree(nx);
			if (trig1 == NULL)
			{
				token tk = trig->tok_type;
				token tok = (tk == SIN_F) ? COS_F : SIN_F;
				trig1 = join(clone(trig->tleft), NULL, fnc[tok].ex);
				if (tk == SIN_F)
					return trig_solution_2(a, b, c, x, dg, part1, part, trig1, trig);
			}
			return trig_solution_2(a, b, c, x, dg, part, part1, trig, trig1);
		}
		clean_tree(a); clean_tree(b); clean_tree(c); clean_tree(f);
	}
	return NULL;
}

#ifdef _EZ80

static Tree* get_condition(Tree* tr, Tree* cond, const char* x, const char* y, Tree** point)
{
	DList vrs = NULL;
	vrs = getvars(cond, vrs);
	if (vrs != NULL && vrs->length == 1 && strstr(vrs->begin->value, y))
	{
		int p = strlen(vrs->begin->value) - strlen(y);
		if (p > 1)
		{
			vrs = clear_dlist(vrs);
			return NULL;
		}
		Tree* n = new_tree("1");
		*point = coefficient_gpe(cond, vrs->begin->value, n);
		clean_tree(n);
		vrs = clear_dlist(vrs);
		return (p == 0) ? clone(tr) : diff(tr, x);
	}
	return NULL;
}

#else

static Tree* get_condition(Tree* tr, Tree* cond, const char* x, const char* y, Tree** point)
{
	char vy[5], vy1[5];
	sprintf(vy1, "%s'(", y);
	sprintf(vy, "%s(", y);
	if (!strcmp(cond->value, vy) || !strcmp(cond->value, vy1))
	{
		*point = clone(cond->tleft);
		return (!strcmp(cond->value, vy)) ? clone(tr) : diff(tr, x);
	}
	return NULL;
}

#endif // _EZ80

static Tree* solve_ode_2(Tree* a, Tree* b, Tree* c, Tree* f, const char* x, const char* y, Tree* cond1, Tree* cond2)
{
	map S = NULL;
	map L = homogenious_2(a, b, c, x, &S);
	Tree* yh = join(join(new_tree("A"), clone(L->begin->tr), fnc[PROD].ex), join(new_tree("B"), clone(L->end->tr), fnc[PROD].ex), fnc[ADD].ex);
	L = clear_map(L);
	Tree* par_sol = solve_exact_2(a, b, c, f, S, x); //recherche solution particulière
	S = clear_map(S);
	if (par_sol == NULL)
	{
		clean_tree(yh);
		Error = push_back_dlist(Error, "No particular solution.");
		return NULL;
	}
	if (strcmp(par_sol->value, "0"))
		yh = simplify(join(yh, par_sol, fnc[ADD].ex));
	else
	{
		yh = simplify(yh);
		clean_tree(par_sol);
	}
	if (cond1 != NULL && cond2 != NULL)
	{
		Tree* p = NULL, * q = NULL;
		b = get_condition(yh, cond1->tleft, x, y, &p);
		if (b == NULL)
		{
			clean_tree(yh); clean_tree(cond1); clean_tree(cond2);
			Error = push_back_dlist(Error, "Error: argument condition.");
			return NULL;
		}
		c = get_condition(yh, cond2->tleft, x, y, &q);
		if (c == NULL)
		{
			clean_tree(b); clean_tree(p); clean_tree(cond1); clean_tree(cond2);
			clean_tree(yh);
			Error = push_back_dlist(Error, "Error: argument condition.");
			return NULL;
		}
		Tree* v = NULL, * w = NULL, * i = NULL, * j = NULL, * k = NULL, * l = NULL, * num1 = NULL, * num2 = NULL, * denom = NULL;
		Tree* cst1 = NULL, * cst2 = NULL, * z = new_tree("0"), * tmp = NULL;
		b = simplify(remplace_var(b, x, p));
		clean_tree(p);
		a = new_tree("1");
		i = coefficient_gpe(b, "A", a);
		j = coefficient_gpe(b, "B", a);
		tmp = coefficient_gpe(b, "A", z);
		cst1 = coefficient_gpe(tmp, "B", z);
		clean_tree(tmp); clean_tree(b);
		c = simplify(remplace_var(c, x, q));
		clean_tree(q);
		k = coefficient_gpe(c, "A", a);
		l = coefficient_gpe(c, "B", a);
		tmp = coefficient_gpe(c, "A", z);
		cst2 = coefficient_gpe(tmp, "B", z);
		clean_tree(tmp);  clean_tree(a); clean_tree(c); clean_tree(z);
		num1 = simplify(join(clone(l), join(clone(cond1->tright), cst1, fnc[SUB].ex), fnc[PROD].ex));
		num1 = join(num1, simplify(join(clone(j), clone(cond2->tright), fnc[PROD].ex)), fnc[SUB].ex);
		num2 = simplify(join(clone(i), join(clone(cond2->tright), cst2, fnc[SUB].ex), fnc[PROD].ex));
		num2 = join(num2, simplify(join(clone(k), clone(cond1->tright), fnc[PROD].ex)), fnc[SUB].ex);
		clean_tree(cond1); clean_tree(cond2);
		denom = simplify(join(join(l, i, fnc[PROD].ex), join(j, k, fnc[PROD].ex), fnc[SUB].ex));
		v = simplify(join(num1, clone(denom), fnc[DIVID].ex));
		w = simplify(join(num2, denom, fnc[DIVID].ex));
		yh = remplace_var(remplace_var(yh, "A", v), "B", w);
		clean_tree(v); clean_tree(w);
		yh = simplify(yh);
	}
	return join(new_tree(y), yh, fnc[EGAL].ex);
}

static Tree* solve_ode(Tree* M, Tree* N, Tree* f, const char* x, const char* y, Tree* cond)
{
	map S = NULL;
	Tree* r = simplify(join(join(clone(M), clone(N), fnc[DIVID].ex), NULL, fnc[NEGATIF].ex));
	Tree* R = simplify(integral(r, x));
	Tree* s = join(new_tree("K"), join(R, NULL, fnc[EXP_F].ex), fnc[PROD].ex);
	S = push_back_map(S, r);
	clean_tree(r);
	Tree* a = new_tree("0");
	Tree* g = solve_exact_2(a, N, M, f, S, x);
	S = clear_map(S);
	if (g == NULL)
	{
		clean_tree(s);
		Error = push_back_dlist(Error, "Error: No particular solution.");
		return NULL;
	}
	s = simplify(join(s, g, fnc[ADD].ex));
	if (cond != NULL)
	{
		Tree* p = NULL;
		Tree* dr = get_condition(s, cond->tleft, x, y, &p);
		if (dr == NULL)
		{
			clean_tree(s); clean_tree(cond);
			Error = push_back_dlist(Error, "Error: argument condition.");
			return NULL;
		}
		a = new_tree("1");
		N = new_tree("0");
		dr = simplify(remplace_var(dr, x, cond->tleft->tright));
		Tree* b = coefficient_gpe(dr, "K", a);
		M = coefficient_gpe(dr, "K", N);
		clean_tree(dr); clean_tree(a); clean_tree(N);
		Tree* k = join(join(clone(cond->tright), M, fnc[SUB].ex), b, fnc[DIVID].ex);
		k = simplify(k);
		s = remplace_var(s, "K", k);
		clean_tree(k); clean_tree(cond);
		s = simplify(s);
	}
	return join(new_tree(y), s, fnc[EGAL].ex);
}

/* analyse */

map analyse_separe(Tree* tr)
{
	map L = NULL;
	Tree* t = tr;
	while (t->tok_type == SEPARATEUR)
	{
		L = push_front_map(L, t->tright);
		t = t->tleft;
	}
	L = push_front_map(L, t);
	return L;
}

Tree* analyse(Tree* tr)
{
	token tk = tr->tok_type;
	if (tk == DERIV_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if ((L->length == 2 && L->end->tr->gtype == VAR) || (L->length == 3 && L->end->back->tr->gtype == VAR && (L->end->tr->gtype == VAR || L->end->tr->gtype == ENT)))
		{
			Tree* res = NULL;
			if (L->end->tr->gtype == ENT)
				res = simplify(diff_n(L->begin->tr, L->end->back->tr->value, (int)tonumber(L->end->tr->value)));
			else if (L->length == 2 || !strcmp(L->end->back->tr->value, L->end->tr->value))
				res = simplify(diff(L->begin->tr, L->end->tr->value));
			else
				res = simplify(diff_partial(L->begin->tr, L->end->back->tr->value, L->end->tr->value));
			L = clear_map(L);
			return pow_transform(res);
		}
		if (L != NULL)
			L = clear_map(L);
		Error = push_back_dlist(Error, "Error: arguments.");
		return NULL;
	}
	else if (tk == TAYLOR_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if (L->length == 4 && L->begin->next->tr->gtype == VAR  && L->end->back->tr->gtype == ENT)
		{
			Tree* res = taylor(L->begin->tr, L->begin->next->tr, L->end->back->tr, L->end->tr);
			L = clear_map(L);
			return res;
		}
		if (L != NULL)
			L = clear_map(L);
		Error = push_back_dlist(Error, "Error: arguments.");
		return NULL;
	}
	else if (tk == TANG_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if (L->length == 3 && L->begin->next->tr->gtype == VAR)
		{
			Tree* res = tangline(L->begin->tr, L->begin->next->tr->value, L->end->tr);
			L = clear_map(L);
			return pow_transform(simplify(res));
		}
		if (L != NULL)
			L = clear_map(L);
		Error = push_back_dlist(Error, "Error: arguments.");
		return NULL;
	}
	else if (tk == INTEGRAL_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if (L->length >=2  && L->begin->next->tr->gtype == VAR)
		{
			Tree* res = integral(L->begin->tr, L->begin->next->tr->value);
			L = clear_map(L);
			if (res == NULL)
			{
				Error = push_back_dlist(Error, "No solution.");
				return NULL;
			}
			return pow_transform(simplify(res));
		}
		if (L != NULL)
			L = clear_map(L);
		Error = push_back_dlist(Error, "Error: arguments.");
		return NULL;
	}
	else if (tk == DESOLVE_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if (L->length == 3 && L->begin->next->tr->gtype == VAR && L->end->tr->gtype == VAR)
		{
			Tree* t = L->begin->tr, * x = L->begin->next->tr, * y = L->end->tr, * cond1 = NULL, * cond2 = NULL;
			Tree* un = new_tree("1");
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
				Tree* a = coefficient_gpe(t->tleft, var_y, un), * b = coefficient_gpe(t->tleft, y1, un);
				L = clear_map(L);
				clean_tree(un);
				return solve_ode(a, b, t->tright, var_x, var_y, cond1);
			}
			if (t->tok_type == LOGIC_AND)
			{
				cond2 = clone(t->tright);
				t = t->tleft;
				if (t->tok_type != LOGIC_AND)
				{
					L = clear_map(L);
					clean_tree(un);
					Error = push_back_dlist(Error, "Error: arguments conditions.");
					return NULL;
				}
				cond1 = clone(t->tright);
				t = t->tleft;
			}
			Tree* f = clone(t->tright);
			t = t->tleft;
			Tree* a = coefficient_gpe(t, y2, un), * b = coefficient_gpe(t, y1, un), * c = coefficient_gpe(t, var_y, un);
			L = clear_map(L);
			clean_tree(un);
			return solve_ode_2(a, b, c, f, var_x, var_y, cond1, cond2);
		}
	}
	else if (tk == EXPAND_F)
	{
		if (tr->tleft->tok_type == SEPARATEUR)
		{
			clean_tree(tr);
			Error = push_back_dlist(Error, "Error: arguments.");
			return NULL;
		}
		TRIG_EXPAND = true;
		LN_EXP_EXPAND = true;
		ALG_EXPAND = true;
		Tree* s = algebraic_expand(tr->tleft);
		clean_noeud(tr);
		return simplify(s);
	}
	else if (tk == FACTOR_F)
	{
		if (tr->tleft->tok_type == SEPARATEUR && tr->tleft->tright->gtype == VAR)
		{
			if (ispoly(tr->tleft->tleft, tr->tleft->tright->value))
			{
				Tree* s = square_free_factor(tr->tleft->tleft, tr->tleft->tright->value);
				clean_tree(tr);
				return s;
			}
			return tr;
		}
		else
		{
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
			if (isconstant(tr->tleft))
			{
				Tree* u = clone(tr->tleft);
				clean_tree(tr);
				return u;
			}
			string vr = variable(tr->tleft);
			if (vr != NULL && ispoly(tr->tleft, vr))
			{
				Tree* s = square_free_factor(tr->tleft->tleft, vr);
				clean_tree(tr); free(vr);
				return s;
			}
			clean_tree(tr);
			Error = push_back_dlist(Error, "Error: Argument : entier/int.");
			return NULL;
		}
	}
	else if (tk == REMAINDER_F || tk == INT_F || tk == GCD_F || tk == POLYSIMP_F)
	{
		map L = analyse_separe(tr->tleft);
		clean_tree(tr);
		if (L->length == 3 && L->end->tr->gtype == VAR)
		{
			map coef_t = polycoeffs(L->begin->tr, L->end->tr->value), coef_a = polycoeffs(L->begin->next->tr, L->end->tr->value), r = NULL;
			clean_tree(tr);
			if (tk == REMAINDER_F)
				r = poly_remainder(coef_t, coef_a);
			else if (tk == INT_F)
				r = poly_quotient(coef_t, coef_a);
			else if (tk == GCD_F)
				r = poly_gcd(coef_t, coef_a);
			else if (tk == POLYSIMP_F)
			{
				Tree* ret = poly_simp(coef_t, coef_a, L->end->tr->value);
				L = clear_map(L);
				return ret;
			}
			coef_t = clear_map(coef_t); coef_a = clear_map(coef_a);
			Tree* ret = polyreconstitute(&r, L->end->tr->value);
			L = clear_map(L);
			return pow_transform(ret);
		}
		if (L != NULL)
			L = clear_map(L);
		Error = push_back_dlist(Error, "Error: arguments.");
		return NULL;
	}
	ALG_EXPAND = true;
	return pow_transform(Contract_pow(simplify(tr)));
}
