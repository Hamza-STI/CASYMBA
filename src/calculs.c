#include "calculs.h"

const char* err_msg[] = { "Err: Args", "Err: No solution", "Err: Args Conditions" };
DList Error = NULL;

static Tree* factor_by_int(Tree* u, const char* x)
{
	for (unsigned i = 1; i <= 10; i++)
	{
		Tree* v = new_tree(tostr(i)), * w = join(new_tree(tostr(i)), NULL, fnc[NEGATIF].ex);
		Tree* r = simplify(remplace_tree(u, x, v)), * s = simplify(remplace_tree(u, x, w));
		bool k = !strcmp(s->value, "0"), j = !strcmp(r->value, "0");
        clean_tree(s); clean_tree(r);
		if (j || k)
		{
			map cf = polycoeffs(u, x), R = NULL;
			R = push_back_map(push_back_map_s(R, new_tree("1")), k ? w : v);
			clean_tree(v); clean_tree(w);
			map Q = poly_quotient(cf, R, INT_F);
			Tree* q = polyreconstitute(&Q, x), * f = polyreconstitute(&R, x);
			r = square_free_factor(q, x);
			cf = clear_map(cf);
			clean_tree(q);
			return join(f, r, fnc[PROD].ex);
		}
		clean_tree(v); clean_tree(w);
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
		coef_u = push_back_map_s(coef_u, q);
		tmp = tmp->next;
	}
	cf = clear_map(cf);
	int k = coef_u->length, i = coef_u->length - 1;
	tmp = coef_u->begin;
	while (i > 0)
	{
		coef_v = push_back_map_s(coef_v, simplify(join(clone(tmp->tr), new_tree(tostr(i)), fnc[PROD].ex)));
		i--;
		tmp = tmp->next;
	}
	map R = poly_gcd(coef_u, coef_v);
	coef_v = clear_map(coef_v);
	map F = poly_quotient(coef_u, R, INT_F);
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
		map q = poly_quotient(F, G, INT_F);
		Tree* s = polyreconstitute(&q, x);
		if (j > 1 && strcmp(s->value, "1"))
			s = join(s, new_tree(tostr(j)), fnc[POW].ex);
		if (strcmp(s->value, "1"))
			P = (P == NULL) ? s : join(P, s, fnc[PROD].ex);
		else
			clean_tree(s);
		map tmp = poly_quotient(R, G, INT_F);
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
	Tree* dtrc = remplace_tree(dtr, vr, point), * trc = remplace_tree(tr, vr, point);
	Tree* tantr = join(join(dtrc, join(new_tree(vr), clone(point), fnc[SUB].ex), fnc[PROD].ex), trc, fnc[ADD].ex);
	clean_tree(dtr);
	return simplify(tantr);
}

/* développements limités : Taylor */

static Tree* taylor_usuelle(Tree* u, const char* vr, Tree* ordre, Tree* point)
{
	Tree* s = simplify(remplace_tree(u, vr, point));
	if (s->tok_type == UNDEF)
	{
		clean_tree(s);
		Error = push_back_dlist(Error, err_msg[1]);
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
		a = simplify(join(a, b, fnc[PROD].ex));
		if (a->tok_type == UNDEF)
		{
			clean_tree(a); clean_tree(s); clean_tree(dtr);
			Error = push_back_dlist(Error, err_msg[1]);
			return NULL; // erreur
		}
		if (strcmp(a->value, "0"))
			s = join(s, clone(a), fnc[ADD].ex);
		clean_tree(a);
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
	if ((u->tok_type == LN_F || u->tok_type == SQRT_F || u->tok_type == POW) && ismonomial(u->tleft, vr->value) && !strcmp(point->value, "0"))
		return clone(u);
	if (usuelle_forme(u->tok_type) || u->tok_type == SQRT_F || u->tok_type == POW)
		return taylor_usuelle(u, vr->value, ordre, point);
	else if (u->tok_type == PROD)
	{
		Tree* v = taylor(u->tleft, vr, ordre, point), * w = taylor(u->tright, vr, ordre, point);
		if (v == NULL || w == NULL)
		{
            clean_tree(v); clean_tree(w);
			Error = push_back_dlist(Error, err_msg[1]);
			return NULL;
		}
		map lv = map_create_add(v), lw = map_create_add(w);
		clean_tree(v); clean_tree(w);
		Tree* s = new_tree("0");
		mapCell* tmp_v = lv->begin, * tmp_w = NULL;
		double g = Eval(ordre);
		while (tmp_v != NULL)
		{
			tmp_w = lw->begin;
			while (tmp_w != NULL)
			{
				Tree* d = join(degree_sv(tmp_v->tr, vr->value), degree_sv(tmp_w->tr, vr->value), fnc[ADD].ex);
				double h = Eval(d);
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
		return simplify(s);
	}
	else if (u->tok_type == ADD || u->tok_type == SUB)
	{
		Tree* v = taylor(u->tleft, vr, ordre, point), * w = taylor(u->tright, vr, ordre, point);
		if (v == NULL || w == NULL)
		{
			clean_tree(v); clean_tree(w);
			Error = push_back_dlist(Error, err_msg[1]);
			return NULL;
		}
		return simplify(join(v, w, u->value));
	}
	return clone(u);
}

/* équations differentielles linéaires */

static Tree* sub_ode(Tree* tr, const char** vrs, map Li)
{
	mapCell* tmp = Li->begin;
	int i = 0;
	while (tmp != NULL)
	{
		tr = remplace_var(tr, vrs[i], tmp->tr);
		++i;
		tmp = tmp->next;
	}
	return tr;
}

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
		*S = push_back_map_s(*S, d);
		L = push_back_map_s(push_back_map_s(L, cs), sn);
		return L;
	}
	Tree* D = simplify(join(clone((b->tok_type == NEGATIF) ? b->tleft : b), new_tree("2"), fnc[POW].ex));
	Tree* e = simplify(join(join(new_tree("4"), clone(a), fnc[PROD].ex), clone(c), fnc[PROD].ex));
	D = simplify(join(D, e, fnc[SUB].ex));
	double d = Eval(D);
	if (d > 0)
	{
		e = (b->tok_type == NEGATIF) ? clone(b->tleft) : join(clone(b), NULL, fnc[NEGATIF].ex);
		Tree* P = simplify(e), * O = simplify(join(D, NULL, fnc[SQRT_F].ex));
		Tree* Z = simplify(join(new_tree("2"), clone(a), fnc[PROD].ex));
		Tree* r1 = simplify(join(join(clone(P), clone(O), fnc[ADD].ex), clone(Z), fnc[DIVID].ex));
		Tree* r2 = simplify(join(join(P, O, fnc[SUB].ex), Z, fnc[DIVID].ex));
		*S = push_back_map(push_back_map(*S, r1), r2);
		Tree* y1 = join(join(r1, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* y2 = join(join(r2, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		L = push_back_map_s(push_back_map_s(L, y1), y2);
	}
	else if (d == 0)
	{
		Tree* com = simplify(join(clone(b), join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex));
		com = simplify(join(com, NULL, fnc[NEGATIF].ex));
		*S = push_back_map(*S, com);
		com = join(join(com, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* y = join(clone(com), new_tree(x), fnc[PROD].ex);
		L = push_back_map_s(push_back_map_s(L, com), y);
		clean_tree(D);
	}
	else if (d < 0)
	{
		e = (b->tok_type == NEGATIF) ? clone(b->tleft) : join(clone(b), NULL, fnc[NEGATIF].ex);
		Tree* com = join(e, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex);
		com = simplify(com);
		*S = push_back_map(*S, com);
		com = join(join(com, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* r = join(join(D, NULL, fnc[NEGATIF].ex), NULL, fnc[SQRT_F].ex);
		r = simplify(join(r, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex));
		*S = push_back_map(*S, r);
		Tree* y1 = join(clone(com), join(join(clone(r), new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
		Tree* y2 = join(com, join(join(r, new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex), fnc[PROD].ex);
		L = push_back_map_s(push_back_map_s(L, y1), y2);
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
	while (tmp_L != NULL)
	{
		Tree* t = clone(tmp_L->tr);
		if (v_ps != NULL)
			t = system_rmp(t, v_ps, rt);
		vrs = getvars(t, vrs);
		if (vrs != NULL && vrs->length == 1)
		{
			map cf = polycoeffs(t, vrs->end->value);
			Tree* q = simplify(join(join(clone(tmp_R->tr), clone(cf->end->tr), fnc[SUB].ex), clone(cf->begin->tr), fnc[DIVID].ex));
			cf = clear_map(cf);
			v_ps = push_back_dlist(v_ps, vrs->end->value);
			rt = push_back_map_s(rt, q);
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
	return rt;
}

static Tree* create_poly(const char* cf, int i, Tree* dg, const char* x)
{
    Tree* w = new_tree(cf);
    if (i == 0)
        return w;
    Tree* v = new_tree(x);
    if (i > 1)
		return join(w, join(v, clone(dg), fnc[POW].ex), fnc[PROD].ex);
	return join(w, v, fnc[PROD].ex);
}

static Tree* poly_solution_2(Tree* a, Tree* b, Tree* c, Tree* part, const char* x, Tree* dg)
{
	Tree* Pl = NULL;
	int w = (int)tonumber(dg->value);
	map cf = NULL, cpl = NULL, sol = NULL;
	DList vr = NULL;
	mapCell* tmp = NULL;
	DListCell* cel_vr = NULL;
	for (int i = w; i >= 0; i--)
		cpl = push_back_map_s(cpl, new_tree("0"));
	for (int i = w; i >= 0; i--)
	{
		char ct[] = { 'M', '0' + i, '\0' };
		Tree* cf_i = coefficient_gpe(part, x, i);
		vr = push_back_dlist(vr, ct);
		cf = push_front_map(cf, cf_i);
		clean_tree(cf_i);
		Tree* z = create_poly(ct, i, dg, x);
		Pl = (Pl == NULL) ? z : join(Pl, z, fnc[ADD].ex);
		if (strcmp(c->value, "0"))
			cpl = map_remplace(cpl, i, join(clone(c), new_tree(ct), fnc[PROD].ex));
		if (i - 1 >= 0 && strcmp(b->value, "0"))
			cpl = map_remplace(cpl, i - 1, join(join(new_tree(tostr(i)), clone(b), fnc[PROD].ex), new_tree(ct), fnc[PROD].ex));
		if (i - 2 >= 0 && strcmp(a->value, "0"))
			cpl = map_remplace(cpl, i - 2, join(join(new_tree(tostr(i * (i - 1))), clone(a), fnc[PROD].ex), new_tree(ct), fnc[PROD].ex));
		dg = simplify(join(dg, new_tree("1"), fnc[SUB].ex));
	}
	clean_tree(dg); clean_tree(a); clean_tree(b); clean_tree(c); clean_tree(part);
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
	bool k = !strcmp(dg->value, "0"), g = !strcmp(dg->value, "1");
	clean_tree(dg);
	if (k || g)
	{
		Tree* c_x1 = g ? coefficient_gpe(part, x, 1) : part, * s_x1 = g ? coefficient_gpe(part, x, 1) : part1;
		Tree* r = coefficient_gpe(trig->tleft, x, 1);
		const char* vr1[] = { "a", "b", "c", "r", "q", "v" };
		map Li = NULL;
		Li = push_back_map_s(push_back_map_s(push_back_map_s(push_back_map_s(push_back_map_s(push_back_map_s(Li, a), b), c), r), c_x1), s_x1);
		Tree* m1 = simplify(sub_ode(to_tree(In2post2("~((a*r^2-c)*q+b*r*v)")), vr1, Li));
		Tree* m3 = simplify(sub_ode(to_tree(In2post2("~((a*r^2-c)*v+b*r*q)")), vr1, Li));
		Tree* d = simplify(sub_ode(to_tree(In2post2("a^2*r^4-2*a*c*r^2+b^2*r^2+c^2")), vr1, Li));
		m1 = simplify(join(m1, clone(d), fnc[DIVID].ex));
		m3 = simplify(join(m3, clone(d), fnc[DIVID].ex));
		if (k)
		{
			clean_tree(d);
			Li = clear_map(Li);
			return join(join(m1, trig, fnc[PROD].ex), join(m3, trig1, fnc[PROD].ex), fnc[ADD].ex);
		}
		Tree* c_x0 = coefficient_gpe(part, x, 0), * s_x0 = coefficient_gpe(part1, x, 0);
		const char* vr2[] = { "a", "b", "c", "r", "m", "n", "p", "u" };
		Li = push_back_map_s(push_back_map_s(push_back_map(push_back_map(pop_back_map(pop_back_map(Li)), m1), m3), c_x0), s_x0);
		Tree* m2 = simplify(sub_ode(to_tree(In2post2("2*a^2*n*r^3+a*(p-b*m)*r^2+r*(~b*u-2*a*c*n+b^2*n)-b*c*m+c*p")), vr2, Li));
		Tree* m4 = simplify(sub_ode(to_tree(In2post2("~2*a^2*m*r^3+r^2*(~a*u-a*b*n)+(2*a*c*m-b^2*m+b*p)*r+c*u-b*c*n")), vr2, Li));
		Li = clear_map(Li);
		m2 = simplify(join(m2, clone(d), fnc[DIVID].ex));
		m4 = simplify(join(m4, d, fnc[DIVID].ex));
		m1 = join(join(m1, new_tree(x), fnc[PROD].ex), m2, fnc[ADD].ex);
		m3 = join(join(m3, new_tree(x), fnc[PROD].ex), m4, fnc[ADD].ex);
		return join(join(m1, trig, fnc[PROD].ex), join(m3, trig1, fnc[PROD].ex), fnc[ADD].ex);
	}
	Error = push_back_dlist(Error, err_msg[1]);
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
			Tree* r = coefficient_gpe(part_exp->tleft, x, 1), * dg = degree_sv(part, x);
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
				int k = R->length;
				clean_tree(f);
				trig = trig_separe(R->begin->tr, x, &part);
				trig1 = trig_separe(R->end->tr, x, &part1);
				R = clear_map(R);
				if (k != 2 || trig == NULL || trig1 == NULL || trig->tok_type == trig1->tok_type || !tree_compare(trig->tleft, trig1->tleft))
				{
					clean_tree(trig); clean_tree(trig1); clean_tree(part1); clean_tree(part);
					Error = push_back_dlist(Error, "Err: excepted form Acos(U)+Bsin(U).");
					return NULL; //retourner une erreur forme attendu Acos(U)+Bsin(U)
				}
			}
			else
			{
				trig = trig_separe(f, x, &part);
				clean_tree(f);
				part1 = new_tree("0");
			}
			Tree* nx = coefficient_gpe(trig->tleft, x, 1), * dg = degree_sv(part, x);
			if (tree_compare(nx, S->end->tr))
				dg = simplify(join(dg, new_tree("1"), fnc[ADD].ex));
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
		*point = coefficient_gpe(cond, vrs->begin->value, 1);
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

static map solve_ode_system(Tree* b, const char* x, Tree* pt, Tree* cond)
{
	b = simplify(remplace_var(b, x, pt));
	clean_tree(pt);
	Tree* i = coefficient_gpe(b, "A", 1), * j = coefficient_gpe(b, "B", 1), * tmp = coefficient_gpe(b, "A", 0);
	Tree* d = simplify(join(clone(cond), coefficient_gpe(tmp, "B", 0), fnc[SUB].ex));
	clean_tree(tmp);  clean_tree(b);
	return push_back_map_s(push_back_map_s(push_back_map_s(NULL, i), j), d);
}

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
		Error = push_back_dlist(Error, err_msg[1]);
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
			Error = push_back_dlist(Error, err_msg[2]);
			return NULL;
		}
		c = get_condition(yh, cond2->tleft, x, y, &q);
		if (c == NULL)
		{
			clean_tree(b); clean_tree(p); clean_tree(cond1); clean_tree(cond2);
			clean_tree(yh);
			Error = push_back_dlist(Error, err_msg[2]);
			return NULL;
		}
		Tree* v = NULL, * w = NULL, * num1 = NULL, * num2 = NULL, * denom = NULL;
		map cf1 = solve_ode_system(b, x, p, cond1->tright), cf2 = solve_ode_system(c, x, q, cond2->tright);
		num1 = simplify(join(join(clone(cf2->begin->next->tr), clone(cond1->tright), fnc[PROD].ex), join(clone(cf1->begin->next->tr), clone(cf2->end->tr), fnc[PROD].ex), fnc[SUB].ex));
		num2 = simplify(join(join(clone(cf1->begin->tr), clone(cond2->tright), fnc[PROD].ex), join(clone(cf2->begin->tr), clone(cf1->end->tr), fnc[PROD].ex), fnc[SUB].ex));
		clean_tree(cond1); clean_tree(cond2);
		denom = simplify(join(join(clone(cf2->begin->next->tr), clone(cf1->begin->tr), fnc[PROD].ex), join(clone(cf1->begin->next->tr), clone(cf2->begin->tr), fnc[PROD].ex), fnc[SUB].ex));
		v = simplify(join(num1, clone(denom), fnc[DIVID].ex));
		w = simplify(join(num2, denom, fnc[DIVID].ex));
		yh = remplace_var(remplace_var(yh, "A", v), "B", w);
		clean_tree(v); clean_tree(w);
		cf1 = clear_map(cf1); cf2 = clear_map(cf2);
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
	S = push_back_map_s(S, r);
	Tree* a = new_tree("0");
	Tree* g = solve_exact_2(a, N, M, f, S, x);
	S = clear_map(S);
	if (g == NULL)
	{
		clean_tree(s);
		Error = push_back_dlist(Error, err_msg[1]);
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
			Error = push_back_dlist(Error, err_msg[2]);
			return NULL;
		}
		dr = simplify(remplace_var(dr, x, p));
		map cf = polycoeffs(dr, x);
		clean_tree(dr);
		Tree* k = simplify(join(join(clone(cond->tright), clone(cf->end->tr), fnc[SUB].ex), clone(cf->begin->tr), fnc[DIVID].ex));
		cf = clear_map(cf);
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
			Tree* s = square_free_factor(tr->tleft->tleft, tr->tleft->tright->value);
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
		if (tk == DERIV_F && ((L->length == 2 && L->end->tr->gtype == VAR) || (L->length == 3 && L->end->back->tr->gtype == VAR && (L->end->tr->gtype == VAR || L->end->tr->gtype == ENT))))
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
		else if (tk == TAYLOR_F && L->length == 4 && L->begin->next->tr->gtype == VAR && L->end->back->tr->gtype == ENT)
		{
			Tree* res = taylor(L->begin->tr, L->begin->next->tr, L->end->back->tr, L->end->tr);
			L = clear_map(L);
			return res;
		}
		else if (tk == TANG_F && L->length == 3 && L->begin->next->tr->gtype == VAR)
		{
			Tree* res = tangline(L->begin->tr, L->begin->next->tr->value, L->end->tr);
			L = clear_map(L);
			return pow_transform(simplify(res));
		}
		else if (tk == INTEGRAL_F && L->length >= 2 && L->begin->next->tr->gtype == VAR)
		{
			L->begin->tr = pow_transform(simplify(L->begin->tr));
			Tree* res = integral(L->begin->tr, L->begin->next->tr->value);
			L = clear_map(L);
			if (res == NULL)
			{
				Error = push_back_dlist(Error, err_msg[1]);
				return NULL;
			}
			return pow_transform(simplify(res));
		}
		else if (tk == DESOLVE_F && L->length == 3 && L->begin->next->tr->gtype == VAR && L->end->tr->gtype == VAR)
		{
			Tree* t = L->begin->tr, * x = L->begin->next->tr, * y = L->end->tr, * cond1 = NULL, * cond2 = NULL;
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
				Tree* a = coefficient_gpe(t->tleft, var_y, 1), * b = coefficient_gpe(t->tleft, y1, 1);
				L = clear_map(L);
				return solve_ode(a, b, t->tright, var_x, var_y, cond1);
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
			Tree* f = clone(t->tright);
			t = t->tleft;
			Tree* a = coefficient_gpe(t, y2, 1), * b = coefficient_gpe(t, y1, 1), * c = coefficient_gpe(t, var_y, 1);
			L = clear_map(L);
			return pow_transform(solve_ode_2(a, b, c, f, var_x, var_y, cond1, cond2));
		}
		else if (REMAINDER_F <= tk && tk <= POLYSIMP_F && L->length == 3 && L->end->tr->gtype == VAR)
		{
			map coef_t = polycoeffs(L->begin->tr, L->end->tr->value), coef_a = polycoeffs(L->begin->next->tr, L->end->tr->value), r = NULL;
			if (tk == POLYSIMP_F)
			{
				Tree* ret = poly_simp(coef_t, coef_a, L->end->tr->value);
				L = clear_map(L);
				return ret;
			}
			else if (tk == GCD_F)
				r = poly_gcd(coef_t, coef_a);
			else
				r = poly_quotient(coef_t, coef_a, tk);
			coef_t = clear_map(coef_t); coef_a = clear_map(coef_a);
			Tree* ret = polyreconstitute(&r, L->end->tr->value);
			L = clear_map(L);
			return pow_transform(ret);
		}
		L = clear_map(L);
		Error = push_back_dlist(Error, err_msg[0]);
		return NULL;
	}
	ALG_EXPAND = true;
	return pow_transform(Contract_pow(simplify(tr)));
}
