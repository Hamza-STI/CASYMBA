#include "calculs.h"

DList Error = NULL;

static Tree* diff(Tree* tr, const char* vr);
static Tree* diff_n(Tree* tr, const char* vr, int k);
static Tree* diff_partial(Tree* tr, const char* vr, const char* vr1);
static Tree* tangline(Tree* tr, const char* vr, Tree* point);
static Tree* taylor(Tree* u, Tree* vr, Tree* ordre, Tree* point);
static Tree* integral(Tree* tr, const char* x);

static Tree* diff(Tree* tr, const char* vr)
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
			if (!isconstant(w))
			{
				Tree* v = numerator_fun(tr);
				Tree* dl = diff(v, vr);
				Tree* dr = diff(w, vr);
				return join(join(join(dl, clone(w), fnc[PROD].ex), join(dr, v, fnc[PROD].ex), fnc[SUB].ex), join(w, new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
			}
			clean_tree(w);
		}
		Tree* dl = diff(tr->tleft, vr);
		Tree* dr = diff(tr->tright, vr);
		if (tok == ADD || tok == SUB)
			return simplify(join(dl, dr, sig));
		if (tok == PROD)
		{
			Tree* t = join(join(dl, clone(tr->tright), fnc[PROD].ex), join(dr, clone(tr->tleft), fnc[PROD].ex), fnc[ADD].ex);
			t->tleft = simplify(t->tleft);
			t->tright = simplify(t->tright);
			return simplify(t);
		}
		if (tok == DIVID)
		{
			Tree* t = join(join(dl, clone(tr->tright), fnc[PROD].ex), join(dr, clone(tr->tleft), fnc[PROD].ex), fnc[SUB].ex);
			t->tleft = simplify(t->tleft);
			t->tright = simplify(t->tright);
			t = join(t, join(clone(tr->tright), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
			return t;
		}
		if (tok == POW)
		{
			if (!strcmp(dr->value, "0"))
			{
				Tree* dtl = simplify(join(clone(tr->tright), dl, fnc[PROD].ex));
				Tree* t = join(clone(tr->tright), new_tree("1"), fnc[SUB].ex);
				Tree* dtr = simplify(join(clone(tr->tleft), t, fnc[POW].ex));
				clean_tree(dr);
				return simplify(join(dtl, dtr, fnc[PROD].ex));
			}
			Tree* dtl = join(clone(tr->tright), join(clone(tr->tleft), join(clone(tr->tright), new_tree("1"), fnc[SUB].ex), fnc[POW].ex), fnc[PROD].ex);
			dtl = join(dtl, dl, fnc[PROD].ex);
			Tree* dtr = join(join(dr, clone(tr), fnc[PROD].ex), join(clone(tr->tleft), NULL, fnc[LN_F].ex), fnc[PROD].ex);
			return simplify(join(dtl, dtr, fnc[ADD].ex));
		}
	}
	else if (op == NEGATION)
		return join(simplify(diff(tr->tleft, vr)), NULL, sig);
	else if (op == FUNCTION)
	{
		if (tok == INTEGRAL_F)
		{
			Tree* t = tr;
			while (t->tleft->tok_type == SEPARATEUR)
				t = t->tleft;
			return clone(t->tleft);
		}
		if (tok == LOGBASE_F)
		{
			Tree* dleft = simplify(diff(tr->tleft->tleft, vr));
			Tree* b = tr->tleft->tright;
			return join(dleft, join(clone(tr->tleft->tleft), join(clone(b), NULL, fnc[LN_F].ex), fnc[PROD].ex), fnc[DIVID].ex);
		}
		Tree* dl = simplify(diff(tr->tleft, vr));
		if (tok == LN_F)
			return join(dl, clone(tr->tleft), fnc[DIVID].ex);
		if (tok == LOG_F)
			return join(dl, join(clone(tr->tleft->tleft), join(new_tree("10"), NULL, fnc[LN_F].ex), fnc[PROD].ex), fnc[DIVID].ex);
		else if (tok == EXP_F)
			return join(dl, clone(tr), fnc[PROD].ex);
		else if (tok == SQRT_F)
			return join(join(new_tree("1"), new_tree("2"), fnc[DIVID].ex), join(dl, clone(tr), fnc[DIVID].ex), fnc[PROD].ex);
		else if (tok == COS_F)
			return join(join(dl, NULL, fnc[NEGATIF].ex), join(clone(tr->tleft), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
		else if (tok == SIN_F)
			return join(dl, join(clone(tr->tleft), NULL, fnc[COS_F].ex), fnc[PROD].ex);
		else if (tok == TAN_F)
			return join(dl, join(join(clone(tr->tleft), NULL, fnc[COS_F].ex), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
		else if (tok == COSH_F)
			return join(dl, join(clone(tr->tleft), NULL, fnc[SINH_F].ex), fnc[PROD].ex);
		else if (tok == SINH_F)
			return join(dl, join(clone(tr->tleft), NULL, fnc[COSH_F].ex), fnc[PROD].ex);
		else if (tok == TANH_F)
			return join(dl, join(join(clone(tr->tleft), NULL, fnc[COSH_F].ex), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
		else if (tok == ACOS_F)
			return join(join(dl, NULL, fnc[NEGATIF].ex), join(join(new_tree("1"), join(clone(tr->tleft), new_tree("2"), fnc[POW].ex), fnc[SUB].ex), NULL, fnc[SQRT_F].ex), fnc[DIVID].ex);
		else if (tok == ASIN_F)
			return join(dl, join(join(new_tree("1"), join(clone(tr->tleft), new_tree("2"), fnc[POW].ex), fnc[SUB].ex), NULL, fnc[SQRT_F].ex), fnc[DIVID].ex);
		else if (tok == ATAN_F)
			return join(dl, join(join(clone(tr->tleft), new_tree("2"), fnc[POW].ex), new_tree("1"), fnc[ADD].ex), fnc[DIVID].ex);
		else if (tok == ACOSH_F)
			return join(dl, join(join(join(clone(tr->tleft), new_tree("1"), fnc[SUB].ex), NULL, fnc[SQRT_F].ex), join(join(clone(tr->tleft), new_tree("1"), fnc[ADD].ex), NULL, fnc[SQRT_F].ex), fnc[PROD].ex), fnc[DIVID].ex);
		else if (tok == ASINH_F)
			return join(dl, join(join(join(clone(tr->tleft), new_tree("2"), fnc[POW].ex), new_tree("1"), fnc[ADD].ex), NULL, fnc[SQRT_F].ex), fnc[DIVID].ex);
		else if (tok == ATANH_F)
			return join(join(dl, NULL, fnc[NEGATIF].ex), join(join(clone(tr->tleft), new_tree("2"), fnc[POW].ex), new_tree("1"), fnc[SUB].ex), fnc[DIVID].ex);
		else if (tok == ABS_F)
			return join(dl, join(clone(tr->tleft), NULL, fnc[SIGN_F].ex), fnc[PROD].ex);
	}
	return join(join(clone(tr), new_tree(vr), fnc[SEPARATEUR].ex), NULL, fnc[DERIV_F].ex);
}

static Tree* diff_n(Tree* tr, const char* vr, int k)
{
    Tree* res = clone(tr);
    int i;
    for (i = 0; i < k; i++)
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
    Tree* dtrc = remplace_tree(dtr, vr, point);
    Tree* trc = remplace_tree(clone(tr), vr, point);
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
		Tree* r = simplify(remplace_tree(dtr, vr, point));
		double f_i = factoriel(i);
		Tree* k = new_tree(tostr(i));
		Tree* a = join(r, new_tree(tostr(f_i)), fnc[DIVID].ex);
		Tree* b = join(simplify(join(new_tree(vr), clone(point), fnc[SUB].ex)), k, fnc[POW].ex);
		Tree* c = simplify(join(a, b, fnc[PROD].ex));
        if (c->tok_type == UNDEF)
		{
			clean_tree(c); clean_tree(s); clean_tree(dtr);
            Error = push_back_dlist(Error, "Erreur de calcul. Non géré.");
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
	{
		Error = push_back_dlist(Error, "Non géré.");
		return NULL;
	}
	if (usuelle_forme(u->tok_type))
	{
		if (u->tleft->tok_type == SQRT_F)
		{
			Tree* z = new_tree("0");
			Tree* R = substitute(u->tleft->tleft, vr, z);
			R = simplify(R);
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
	{
		return taylor_usuelle(u, vr->value, ordre, point);
	}
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
		if (v == NULL && w == NULL)
        {
            Error = push_back_dlist(Error, "Non géré.");
            return NULL;
        }
		if (v == NULL && w != NULL)
			return simplify(join(clone(u->tleft), w, u->value));
		if (v != NULL && w == NULL)
			return simplify(join(v, clone(u->tright), u->value));
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
		L = push_back_map(L, cs);
		L = push_back_map(L, sn);
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
		Tree* P = simplify(e);
		Tree* O = simplify(join(D, NULL, fnc[SQRT_F].ex));
		Tree* Z = simplify(join(new_tree("2"), clone(a), fnc[PROD].ex));
		Tree* r1 = join(join(clone(P), clone(O), fnc[ADD].ex), clone(Z), fnc[DIVID].ex);
		Tree* r2 = join(join(P, O, fnc[SUB].ex), Z, fnc[DIVID].ex);
		r1 = simplify(r1);
		r2 = simplify(r2);
		*S = push_back_map(*S, r1);
		*S = push_back_map(*S, r2);
		Tree* y1 = join(join(r1, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* y2 = join(join(r2, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		L = push_back_map(L, y1);
		L = push_back_map(L, y2);
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
		L = push_back_map(L, com);
		L = push_back_map(L, y);
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
		r = join(r, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex);
		r = simplify(r);
		*S = push_back_map(*S, r);
		Tree* y1 = join(clone(com), join(join(clone(r), new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
		Tree* y2 = join(com, join(join(r, new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex), fnc[PROD].ex);
		L = push_back_map(L, y1);
		L = push_back_map(L, y2);
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
		tr = remplace_tree(tr, tmp->value, tmp_L->tr);
		tmp_L = tmp_L->next;
		tmp = tmp->next;
	}
	return tr;
}

static map solve_system(map L, map R)
{
	mapCell* tmp_L = L->begin, * tmp_R = R->begin;
	DList vrs = NULL, v_ps = NULL;
	map rt = NULL;
	Tree* z = new_tree("0"), * o = new_tree("1");
	while (tmp_L != NULL)
	{
		Tree* t = tmp_L->tr;
		if (v_ps != NULL)
			t = system_rmp(t, v_ps, rt);
		vrs = getvars(t, vrs);
		if (vrs != NULL && vrs->length == 1)
		{
			Tree* a = coefficient_gpe(t, vrs->end->value, o);
			Tree* b = coefficient_gpe(t, vrs->end->value, z);
			Tree* q = simplify(join(clone(tmp_R->tr), b, fnc[SUB].ex));
			q = simplify(join(q, a, fnc[DIVID].ex));
			v_ps = push_back_dlist(v_ps, vrs->end->value);
			rt = push_back_map(rt, q);
			clean_tree(q);
		}
		else if (vrs == NULL)
			rt = push_back_map(rt, t);
		vrs = clear_dlist(vrs);
		tmp_L = tmp_L->next;
		tmp_R = tmp_R->next;
	}
	v_ps = clear_dlist(v_ps);
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
	sol = solve_system(cpl, cf);
	cpl = clear_map(cpl); cf = clear_map(cf);
	tmp = sol->begin;
	cel_vr = vr->begin;
	while (tmp != NULL)
	{
		Pl = remplace_tree(Pl, cel_vr->value, tmp->tr);
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
    Error = push_back_dlist(Error, "Non géré.");
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
			bool with = false;
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
			Tree* r = coefficient_gpe(part_exp->tleft, x, o);
			clean_tree(o);
			while (tmp != NULL)
			{
				if (tree_compare(r, tmp->tr))
				{
					with = true;
					break;
				}
				tmp = tmp->next;
			}
			Tree* dg = degree_sv(part, x);
			if (with)
			{
				if (strcmp(a->value, "0") && S->length == 1)
					dg = simplify(join(dg, new_tree("2"), fnc[ADD].ex));
				else
					dg = simplify(join(dg, new_tree("1"), fnc[ADD].ex));
			}
			return exp_solution_2(a, b, c, x, dg, part, part_exp, r);
		}
		else if ((sn || cs) && !e)
		{
			Tree* trig = NULL, * part = NULL, * part1 = NULL, * trig1 = NULL;
			bool with = false;
			if (f->tok_type == PROD && (f->tleft->tok_type == ADD || f->tleft->tok_type == SUB || f->tright->tok_type == ADD || f->tright->tok_type == SUB))
			{
				TRIG_EXPAND = false;
				Tree* F = expand(f);
				Tree* p = f->parent;
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
                    Error = push_back_dlist(Error, "Erreur : forme attendue Acos(U)+Bsin(U).");
					return NULL; //retourner une erreur forme attendu Acos(U)+Bsin(U)
				}
				trig = trig_separe(R->begin->tr, x, &part);
				trig1 = trig_separe(R->end->tr, x, &part1);
				R = clear_map(R);
				if (trig == NULL || trig1 == NULL || trig->tok_type == trig1->tok_type || !tree_compare(trig->tleft, trig1->tleft))
				{
					clean_tree(trig);
					clean_tree(trig1);
					clean_tree(part1);
					clean_tree(part);
                    Error = push_back_dlist(Error, "Erreur : forme attendue Acos(U)+Bsin(U).");
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
			Tree* nx = coefficient_gpe(trig->tleft, x, ng);
			Tree* dg = degree_sv(part, x);
			if (tree_compare(nx, S->end->tr))
				with = true;
			clean_tree(ng);
			clean_tree(nx);
			if (with && trig->tok_type == COS_F)
				dg = simplify(join(dg, new_tree("1"), fnc[ADD].ex));
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
		Error = push_back_dlist(Error, "Pas de solution particulière. Non géré.");
		return NULL;
	}
	if (strcmp(par_sol->value, "0"))
        yh = simplify(join(yh, par_sol, fnc[ADD].ex));
    else
    {
        clean_tree(par_sol);
    }
	if (cond1 != NULL && cond2 != NULL)
	{
        Tree* p = NULL, * q = NULL;
        b = get_condition(yh, cond1->tleft, x, y, &p);
        if (b == NULL)
        {
            clean_tree(yh); clean_tree(cond1); clean_tree(cond2);
			Error = push_back_dlist(Error, "Erreur argument condition.");
            return NULL;
        }
        c = get_condition(yh, cond2->tleft, x, y, &q);
        if (c == NULL)
        {
            clean_tree(b); clean_tree(p); clean_tree(cond1); clean_tree(cond2);
            clean_tree(yh);
			Error = push_back_dlist(Error, "Erreur argument condition.");
            return NULL;
        }
        Tree* v = NULL, * w = NULL, * i = NULL, * j = NULL, * k = NULL, * l = NULL, * num1 = NULL, * num2 = NULL, * denom = NULL;
        Tree* cst1 = NULL, * cst2 = NULL, * z = new_tree("0"), * tmp = NULL;
        b = simplify(remplace_tree(b, x, p));
        clean_tree(p);
		a = new_tree("1");
        i = coefficient_gpe(b, "A", a);
        j = coefficient_gpe(b, "B", a);
        tmp = coefficient_gpe(b, "A", z);
        cst1 = coefficient_gpe(tmp, "B", z);
        clean_tree(tmp); clean_tree(b);
        c = simplify(remplace_tree(c, x, q));
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
        yh = remplace_tree(yh, "A", v);
        yh = remplace_tree(yh, "B", w);
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
			Error = push_back_dlist(Error, "Pas de solution particulière. Non géré.");
		return NULL;
	}
	s = simplify(join(s, g, fnc[ADD].ex));
	if (cond != NULL)
	{
        Tree* p = NULL;
		Tree *dr = get_condition(s, cond->tleft, x, y, &p);
        if (dr == NULL)
        {
            clean_tree(s); clean_tree(cond);
			Error = push_back_dlist(Error, "Erreur argument condition.");
		    return NULL;
        }
        a = new_tree("1");
		N = new_tree("0");
		dr = remplace_tree(dr, x, cond->tleft->tright);
        dr = simplify(dr);
        Tree* b = coefficient_gpe(dr, "K", a);
        M = coefficient_gpe(dr, "K", N);
        clean_tree(dr); clean_tree(a); clean_tree(N);
        Tree* k = join(join(clone(cond->tright), M, fnc[SUB].ex), b, fnc[DIVID].ex);
        k = simplify(k);
        s = remplace_tree(s, "K", k);
        clean_tree(k); clean_tree(cond);
        s = simplify(s);
	}
	return join(new_tree(y), s, fnc[EGAL].ex);
}

/* integrals */

static Tree* integrals_prod_trigo_monomiale(Tree* f, const char* x)
{
	if (f->tok_type == PROD)
	{
		Tree* u = f->tleft, * v = f->tright;
		if (!strcmp(u->value, x) && v->tok_type == COS_F)
		{
			Tree* d = degree_sv(v->tleft, x);
			if (!strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, d);
				Tree* o = join(clone(v), simplify(join(clone(a), new_tree("2"), fnc[POW].ex)), fnc[DIVID].ex);
				Tree* z = join(new_tree(x), join(clone(v->tleft), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
				z = join(z, a, fnc[DIVID].ex);
				clean_tree(d);
				return join(o, z, fnc[ADD].ex);
			}
			clean_tree(d);
		}
		else if (!strcmp(u->value, x) && v->tok_type == SIN_F)
		{
			Tree* d = degree_sv(v->tleft, x);
			if (!strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, d);
				Tree* o = join(clone(v), simplify(join(clone(a), new_tree("2"), fnc[POW].ex)), fnc[DIVID].ex);
				Tree* z = join(new_tree(x), join(clone(v->tleft), NULL, fnc[COS_F].ex), fnc[PROD].ex);
				z = join(z, a, fnc[DIVID].ex);
				clean_tree(d);
				return join(o, z, fnc[SUB].ex);
			}
			clean_tree(d);
		}
		else if (u->tok_type == POW && u->tright->gtype == ENT && !strcmp(u->tleft->value, x))
		{
			if (v->tok_type == COS_F)
			{
				Tree* d = degree_sv(v->tleft, x);
				if (!strcmp(d->value, "1"))
				{
					Tree* a = coefficient_gpe(v->tleft, x, d);
					Tree* n1 = simplify(join(new_tree(x), join(clone(u->tright), new_tree("1"), fnc[SUB].ex), fnc[POW].ex));
					Tree* sn = join(clone(v->tleft), NULL, fnc[SIN_F].ex);
					Tree* t = join(n1, clone(sn), fnc[PROD].ex);
					Tree* s = join(join(clone(u), sn, fnc[PROD].ex), clone(a), fnc[DIVID].ex);
					Tree* r = join(s, join(simplify(join(clone(u->tright), a, fnc[DIVID].ex)), integrals_prod_trigo_monomiale(t, x), fnc[PROD].ex), fnc[SUB].ex);
					clean_tree(t); clean_tree(d);
					return r;
				}
				clean_tree(d);
			}
			else if (v->tok_type == SIN_F)
			{
				Tree* d = degree_sv(v->tleft, x);
				if (!strcmp(d->value, "1"))
				{
					Tree* a = coefficient_gpe(v->tleft, x, d);
					Tree* n1 = simplify(join(new_tree(x), join(clone(u->tright), new_tree("1"), fnc[SUB].ex), fnc[POW].ex));
					Tree* cs = join(clone(v->tleft), NULL, fnc[COS_F].ex);
					Tree* t = join(n1, clone(cs), fnc[PROD].ex);
					Tree* s = join(join(clone(u), cs, fnc[PROD].ex), clone(a), fnc[DIVID].ex);
					Tree* r = join(join(simplify(join(clone(u->tright), a, fnc[DIVID].ex)), integrals_prod_trigo_monomiale(t, x), fnc[PROD].ex), s, fnc[SUB].ex);
					clean_tree(t); clean_tree(d);
					return r;
				}
				clean_tree(d);
			}
		}
	}
	return NULL;
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

static Tree* integral_table(Tree* f, const char* x)
{
	token tk = f->tok_type;
	if (tk == DERIV_F)
	{
		Tree* t = f;
		while (t->tleft->tok_type == SEPARATEUR)
			t = t->tleft;
		return clone(t->tleft);
	}
	if (!found_element(f, x))
		return join(clone(f), new_tree(x), fnc[PROD].ex);
	else if (!strcmp(f->value, x))
		return join(join(clone(f), new_tree("2"), fnc[POW].ex), new_tree("2"), fnc[DIVID].ex);
	if (tk == SINH_F && ismonomial(f->tleft, x))
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			return join(join(clone(f->tleft), NULL, fnc[COSH_F].ex), a, fnc[DIVID].ex);
		}
		clean_tree(d);
	}
	else if (tk == COSH_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			return join(join(clone(f->tleft), NULL, fnc[SINH_F].ex), a, fnc[DIVID].ex);
		}
		clean_tree(d);
	}
	else if (tk == SIN_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			d = join(join(clone(f->tleft), NULL, fnc[COS_F].ex), NULL, fnc[NEGATIF].ex);
			return join(d, a, fnc[DIVID].ex);
		}
		clean_tree(d);
	}
	else if (tk == COS_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			return join(join(clone(f->tleft), NULL, fnc[SIN_F].ex), a, fnc[DIVID].ex);
		}
		clean_tree(d);
	}
	else if (tk == ACOS_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			d = join(new_tree("1"), join(join(clone(a), new_tree(x), fnc[PROD].ex), new_tree("2"), fnc[POW].ex), fnc[SUB].ex);
			d = join(join(d, NULL, fnc[SQRT_F].ex), a, fnc[DIVID].ex);
			return join(join(new_tree(x), clone(f), fnc[PROD].ex), d, fnc[SUB].ex);
		}
		clean_tree(d);
	}
	else if (tk == ASIN_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			d = join(new_tree("1"), join(join(clone(a), new_tree(x), fnc[PROD].ex), new_tree("2"), fnc[POW].ex), fnc[SUB].ex);
			d = join(join(d, NULL, fnc[SQRT_F].ex), a, fnc[DIVID].ex);
			return join(join(new_tree(x), clone(f), fnc[PROD].ex), d, fnc[ADD].ex);
		}
		clean_tree(d);
	}
	else if (tk == EXP_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (!strcmp(d->value, "1"))
		{
			Tree* a = coefficient_gpe(f->tleft, x, d);
			clean_tree(d);
			return join(join(clone(f->tleft), NULL, fnc[EXP_F].ex), a, fnc[DIVID].ex);
		}
		clean_tree(d);
	}
	else if (tk == LN_F)
	{
		Tree* d = degree_sv(f->tleft, x);
		if (ismonomial(f->tleft, x))
			return join(new_tree(x), join(clone(f), d, fnc[SUB].ex), fnc[PROD].ex);
		if (!strcmp(d->value, "1"))
		{
			clean_tree(d);
			Tree* z = new_tree("0"), * o = new_tree("1");
			Tree* a = coefficient_gpe(f->tleft, x, o), * b = coefficient_gpe(f->tleft, x, z);
			clean_tree(z); clean_tree(o);
			return join(join(join(new_tree(x), join(b, a, fnc[DIVID].ex), fnc[ADD].ex), clone(f), fnc[PROD].ex), new_tree(x), fnc[SUB].ex);
		}
		else if (!strcmp(d->value, "2"))
		{
			token tk = f->tleft->tok_type;
			if (tk == ADD || tk == SUB)
			{
				Tree* z = new_tree("0"), * o = new_tree("1");
				Tree* a = coefficient_gpe(f->tleft, x, d), * b = coefficient_gpe(f->tleft, x, o), * c = coefficient_gpe(f->tleft, x, z);
				clean_tree(z); clean_tree(o); clean_tree(d);
				if (!strcmp(b->value, "0"))
				{
					if (a->tok_type == NEGATIF)
						clean_noeud(a);
					if (c->tok_type == NEGATIF)
						clean_noeud(c);
					a = join(a, NULL, fnc[SQRT_F].ex);
					c = join(c, NULL, fnc[SQRT_F].ex);
					Tree* p = join(new_tree(x), f, fnc[PROD].ex);
					Tree* q = join(join(new_tree("2"), clone(c), fnc[PROD].ex), clone(a), fnc[DIVID].ex);
					q = join(q, join(join(join(a, new_tree(x), fnc[PROD].ex), c, fnc[DIVID].ex), NULL, fnc[ATAN_F].ex), fnc[PROD].ex);
					return join(join(p, q, fnc[ADD].ex), join(new_tree("2"), new_tree(x), fnc[PROD].ex), fnc[SUB].ex);
				}
				z = join(join(join(new_tree("4"), a, fnc[PROD].ex), c, fnc[PROD].ex), join(b, new_tree("2"), fnc[POW].ex), fnc[SUB].ex);
				d = join(z, NULL, fnc[SQRT_F].ex);
				d = join(join(join(new_tree("2"), join(clone(a), new_tree(x), fnc[PROD].ex), fnc[PROD].ex), b, fnc[ADD].ex), d, fnc[DIVID].ex);
				Tree* p = join(join(clone(d), clone(a), fnc[DIVID].ex), join(d, NULL, fnc[ATAN_F].ex), fnc[PROD].ex);
				p = join(p, join(new_tree("2"), new_tree(x), fnc[PROD].ex), fnc[SUB].ex);
				Tree* q = join(join(clone(b), join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex), new_tree(x), fnc[ADD].ex);
				return join(p, join(q, clone(f), fnc[PROD].ex), fnc[ADD].ex);
			}
		}

		clean_tree(d);
	}
	else if (tk == SQRT_F)
	{
		Tree* u = f->tleft;
		if (ispoly(u, x))
		{
			Tree* d = degree_sv(u, x);
			if (!strcmp(d->value, "1"))
			{

				Tree* a = coefficient_gpe(u, x, d);
				Tree* w = join(new_tree("3"), new_tree("2"), fnc[DIVID].ex);
				clean_tree(d);
				return join(join(join(new_tree("2"), clone(u), fnc[PROD].ex), w, fnc[POW].ex), join(new_tree("3"), a, fnc[PROD].ex), fnc[DIVID].ex);
			}
			else if (!strcmp(d->value, "2"))
			{
				Tree* z = new_tree("0"), * o = new_tree("1"), * t = NULL;
				Tree* a = coefficient_gpe(u, x, d);
				Tree* b = coefficient_gpe(u, x, o);
				Tree* c = coefficient_gpe(u, x, z);
				clean_tree(z); clean_tree(o); clean_tree(d);
				o = join(join(new_tree("2"), new_tree(x), fnc[PROD].ex), clone(a), fnc[PROD].ex);
				o = simplify(join(o, clone(b), fnc[ADD].ex));
				z = join(join(new_tree("4"), clone(a), fnc[PROD].ex), c, fnc[PROD].ex);
				z = simplify(join(z, join(b, new_tree("2"), fnc[POW].ex), fnc[SUB].ex));
				if (a->tok_type == NEGATIF)
				{
					t = join(new_tree("8"), join(clone(a->tleft), join(new_tree("3"), new_tree("2"), fnc[DIVID].ex), fnc[POW].ex), fnc[PROD].ex);
					d = join(new_tree("2"), join(clone(a->tleft), NULL, fnc[SQRT_F].ex), fnc[PROD].ex);
					d = join(clone(o), join(d, clone(f), fnc[PROD].ex), fnc[DIVID].ex);
					d = join(d, NULL, fnc[ATAN_F].ex);
				}
				else
				{
					t = join(new_tree("8"), join(clone(a), join(new_tree("3"), new_tree("2"), fnc[DIVID].ex), fnc[POW].ex), fnc[PROD].ex);
					d = join(new_tree("2"), join(clone(a), NULL, fnc[SQRT_F].ex), fnc[PROD].ex);
					d = join(join(d, clone(f), fnc[PROD].ex), clone(o), fnc[ADD].ex);
					d = join(join(d, NULL, fnc[ABS_F].ex), NULL, fnc[LN_F].ex);
				}
				z = join(z, t, fnc[DIVID].ex);
				o = join(o, join(new_tree("4"), a, fnc[PROD].ex), fnc[DIVID].ex);
				return join(join(o, clone(f), fnc[PROD].ex), join(z, d, fnc[PROD].ex), fnc[ADD].ex);
			}
			clean_tree(d);
		}
	}
	else if (tk == PROD)
	{
		Tree* cst = constant(f);
		if (strcmp(cst->value, "1"))
		{
			Tree* T = pow_transform(term(f));
			Tree* s = integral(T, x);
			clean_tree(T);
			if (s == NULL)
			{
				clean_tree(cst);
				return s;
			}
			return join(cst, s, fnc[PROD].ex);
		}
		Tree* u = f->tleft;
		Tree* v = f->tright;
		clean_tree(cst);
		token utok = u->tok_type, vtok = v->tok_type;
		if (ispoly(u, x))
		{
			if (vtok == EXP_F)
			{
				Tree* du = degree_sv(u, x), * dv = degree_sv(v->tleft, x);
				if (!strcmp(dv->value, "1"))
				{
					if (!strcmp(du->value, "1"))
					{
						Tree* a = coefficient_gpe(v->tleft, x, du);
						Tree* z = join(new_tree("1"), join(clone(a), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
						Tree* o = join(join(a, new_tree(x), fnc[PROD].ex), new_tree("1"), fnc[SUB].ex);
						o = join(z, o, fnc[PROD].ex);
						clean_tree(du); clean_tree(dv);
						return join(o, clone(v), fnc[PROD].ex);
					}
					else
					{
						Tree* a = coefficient_gpe(v->tleft, x, du);
						Tree* z = join(join(new_tree("1"), a, fnc[DIVID].ex), clone(f), fnc[PROD].ex);
						Tree* d = simplify(join(clone(du), new_tree("1"), fnc[SUB].ex));
						Tree* o = join(join(new_tree(x), d, fnc[POW].ex), clone(v), fnc[PROD].ex);
						Tree* q = integral_table(o, x);
						clean_tree(o);
						return join(z, join(join(du, dv, fnc[DIVID].ex), q, fnc[PROD].ex), fnc[SUB].ex);
					}
				}
				clean_tree(du);
				clean_tree(dv);
			}
			else if (vtok == COS_F || vtok == SIN_F)
			{
				return integrals_prod_trigo_monomiale(f, x);
			}
			else if (((vtok == POW && isdemi(v->tright)) || vtok == SQRT_F) && ispoly(v->tleft, x) && !strcmp(u->value, x))
			{
				Tree* dv = degree_sv(v->tleft, x);
				if (!strcmp(dv->value, "1"))
				{
					Tree* a = coefficient_gpe(v->tleft, x, dv), * z = new_tree("0");
					Tree* b = coefficient_gpe(v->tleft, x, z);
					Tree* aa = simplify(join(clone(a), new_tree("2"), fnc[POW].ex));
					Tree* bb = simplify(join(join(new_tree("2"), NULL, fnc[NEGATIF].ex), join(clone(b), new_tree("2"), fnc[POW].ex), fnc[PROD].ex));
					clean_tree(dv); clean_tree(z);
					z = join(new_tree("3"), join(clone(aa), join(new_tree(x), new_tree("2"), fnc[POW].ex), fnc[PROD].ex), fnc[PROD].ex);
					z = join(bb, join(join(simplify(join(a, b, fnc[PROD].ex)), new_tree(x), fnc[PROD].ex), simplify(z), fnc[ADD].ex), fnc[ADD].ex);
					dv = join(new_tree("2"), join(new_tree("15"), aa, fnc[PROD].ex), fnc[DIVID].ex);
					return join(join(simplify(dv), z, fnc[PROD].ex), clone(v), fnc[PROD].ex);
				}
				clean_tree(dv);
			}
			else if (vtok == LN_F)
			{
				Tree* d = degree_sv(v->tleft, x);
				if (ismonomial(v->tleft, x))
				{
					if (utok == POW && u->tright->gtype == ENT && !strcmp(d->value, "1"))
					{
						Tree* m = join(clone(u->tright), new_tree("1"), fnc[ADD].ex);
						Tree* r = join(join(new_tree(x), clone(m), fnc[POW].ex), clone(m), fnc[DIVID].ex);
						Tree* s = join(clone(v), join(new_tree("1"), m, fnc[DIVID].ex), fnc[SUB].ex);
						return join(r, s, fnc[PROD].ex);
					}
					Tree* du = simplify(join(degree_sv(u, x), new_tree("1"), fnc[ADD].ex));
					Tree* z = join(clone(v), clone(du), fnc[DIVID].ex);
					d = join(d, join(du, new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
					return join(join(new_tree(x), clone(du), fnc[POW].ex), join(z, d, fnc[SUB].ex), fnc[PROD].ex);
				}
				if (!strcmp(u->value, x) && !strcmp(d->value, "1"))
				{
					clean_tree(d);
					Tree* z = new_tree("0"), * o = new_tree("1");
					Tree* a = coefficient_gpe(v->tleft, x, o), * b = coefficient_gpe(v->tleft, x, z);
					clean_tree(z);
					clean_tree(o);
					z = join(clone(b), new_tree(x), fnc[PROD].ex);
					z = join(z, simplify(join(new_tree("2"), clone(a), fnc[PROD].ex)), fnc[DIVID].ex);
					z = join(z, join(join(new_tree(x), new_tree("2"), fnc[POW].ex), new_tree("4"), fnc[DIVID].ex), fnc[SUB].ex);
					o = join(join(b, new_tree("2"), fnc[POW].ex), simplify(join(a, new_tree("2"), fnc[POW].ex)), fnc[DIVID].ex);
					o = join(join(new_tree(x), new_tree("2"), fnc[POW].ex), simplify(o), fnc[SUB].ex);
					o = join(join(o, clone(v), fnc[PROD].ex), new_tree("2"), fnc[DIVID].ex);
					return join(z, o, fnc[ADD].ex);
				}
				else if (!strcmp(u->value, x) && !strcmp(d->value, "2"))
				{
					clean_tree(d);
					Tree* z = new_tree("0"), * o = new_tree("1"), * t = new_tree("2");
					Tree* a = coefficient_gpe(v->tleft, x, t), * b = coefficient_gpe(v->tleft, x, o), * c = coefficient_gpe(v->tleft, x, z);
					clean_tree(z); clean_tree(o); clean_tree(t);
					if (!strcmp(b->value, "0"))
					{
						clean_tree(b);
						z = join(join(join(new_tree(x), new_tree("2"), fnc[POW].ex), new_tree("2"), fnc[DIVID].ex), NULL, fnc[NEGATIF].ex);
						o = join(join(new_tree(x), new_tree("2"), fnc[POW].ex), join(a, c, fnc[DIVID].ex), fnc[SUB].ex);
						o = join(join(o, clone(f), fnc[PROD].ex), new_tree("2"), fnc[DIVID].ex);
						return join(z, o, fnc[ADD].ex);
					}
					return NULL;
				}
				clean_tree(d);
			}
			else if (vtok == POW)
			{
				if (v->tleft->tok_type == LN_F)
				{
					Tree* m = simplify(join(exponent(u), new_tree("1"), fnc[ADD].ex)), * n = simplify(join(exponent(v), new_tree("1"), fnc[SUB].ex));
					Tree* r = join(join(join(base(u), m, fnc[POW].ex), clone(v), fnc[PROD].ex), clone(m), fnc[DIVID].ex);
					Tree* s = NULL, *p = NULL;
					if (!strcmp(n->value, "1"))
						p = join(clone(u), clone(v->tleft), fnc[PROD].ex);
					else
						p = join(clone(u), join(clone(v->tleft), clone(n), fnc[POW].ex), fnc[PROD].ex);
					s = integral_table(p, x);
					clean_tree(p);
					clean_tree(n);
					return join(r, join(join(exponent(v), m, fnc[DIVID].ex), s, fnc[PROD].ex), fnc[SUB].ex);
				}
			}
		}
		if (utok == COS_F && vtok == SIN_F)
		{
			Tree* du = degree_sv(u->tleft, x), * dv = degree_sv(v->tleft, x);
			if (tree_compare(u->tleft, v->tleft) && !strcmp(du->value, "1"))
			{
				Tree* a = coefficient_gpe(u->tleft, x, du);
				Tree* t = join(join(clone(u), new_tree("2"), fnc[POW].ex), NULL, fnc[NEGATIF].ex);
				clean_tree(du); clean_tree(dv);
				return join(t, join(new_tree("2"), a, fnc[PROD].ex), fnc[DIVID].ex);
			}
			else if (tree_compare(du, dv) && !strcmp(du->value, "1"))
			{
				Tree* a = coefficient_gpe(u->tleft, x, du), * b = coefficient_gpe(v->tleft, x, du);
				Tree* ab = simplify(join(clone(a), clone(b), fnc[ADD].ex)), * ab_ = simplify(join(a, b, fnc[SUB].ex));
				Tree* s = join(join(clone(ab_), new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex);
				Tree* r = join(join(clone(ab), new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex);
				s = join(s, simplify(join(new_tree("2"), ab_, fnc[PROD].ex)), fnc[DIVID].ex);
				r = join(r, simplify(join(new_tree("2"), ab, fnc[PROD].ex)), fnc[DIVID].ex);
				clean_tree(du); clean_tree(dv);
				return join(s, r, fnc[SUB].ex);
			}
			clean_tree(du); clean_tree(dv);
		}
		else if (vtok == EXP_F && utok == COS_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, d), * b = coefficient_gpe(u->tleft, x, c);
				clean_tree(c);
				clean_tree(d);
				Tree* z = join(join(clone(a), new_tree("2"), fnc[POW].ex), join(clone(b), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				z = join(join(new_tree("1"), simplify(z), fnc[DIVID].ex), clone(v), fnc[PROD].ex);
				Tree* o = join(b, join(clone(u->tleft), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
				Tree* p = join(join(a, clone(u), fnc[PROD].ex), o, fnc[ADD].ex);
				return join(z, p, fnc[PROD].ex);
			}
		}
		else if (utok == EXP_F && vtok == SIN_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, d), * b = coefficient_gpe(u->tleft, x, c);
				clean_tree(c); clean_tree(d);
				Tree* z = join(join(clone(a), new_tree("2"), fnc[POW].ex), join(clone(b), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				z = join(join(new_tree("1"), simplify(z), fnc[DIVID].ex), clone(u), fnc[PROD].ex);
				Tree* o = join(b, join(clone(v->tleft), NULL, fnc[COS_F].ex), fnc[PROD].ex);
				Tree* p = join(a, clone(v), fnc[PROD].ex);
				p = join(p, o, fnc[SUB].ex);
				return join(z, p, fnc[PROD].ex);
			}
		}
		else if (utok == COSH_F && vtok == EXP_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, c), * b = coefficient_gpe(u->tleft, x, c);
				clean_tree(c); clean_tree(d);
				if (tree_compare(u->tleft, v->tleft))
				{
					clean_tree(b);
					Tree* f = join(join(new_tree("2"), clone(v->tleft), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
					Tree* z = join(simplify(f), join(new_tree("4"), a, fnc[PROD].ex), fnc[DIVID].ex);
					return join(z, join(new_tree(x), new_tree("2"), fnc[DIVID].ex), fnc[ADD].ex);
				}
				else
				{
					Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
					r = join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[SUB].ex);
					c = join(a, join(clone(u->tleft), NULL, fnc[COSH_F].ex), fnc[PROD].ex);
					d = join(b, join(clone(u->tleft), NULL, fnc[SINH_F].ex), fnc[PROD].ex);
					return join(join(clone(v), simplify(r), fnc[DIVID].ex), join(c, d, fnc[SUB].ex), fnc[PROD].ex);
				}
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == EXP_F && vtok == SINH_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(u->tleft, x, c), * b = coefficient_gpe(v->tleft, x, c);
				clean_tree(c); clean_tree(d);
				if (tree_compare(u->tleft, v->tleft))
				{
					clean_tree(b);
					Tree* f = join(join(new_tree("2"), clone(u->tleft), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
					Tree* z = join(simplify(f), join(new_tree("4"), a, fnc[PROD].ex), fnc[DIVID].ex);
					return join(z, join(new_tree(x), new_tree("2"), fnc[DIVID].ex), fnc[SUB].ex);
				}
				else
				{
					Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
					r = join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[SUB].ex);
					c = join(b, join(clone(v->tleft), NULL, fnc[COSH_F].ex), fnc[PROD].ex);
					d = join(a, join(clone(v->tleft), NULL, fnc[SINH_F].ex), fnc[PROD].ex);
					return join(join(clone(u), simplify(r), fnc[DIVID].ex), join(d, c, fnc[SUB].ex), fnc[PROD].ex);
				}
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == COS_F && vtok == COSH_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(u->tleft, x, c), * b = coefficient_gpe(v->tleft, x, c);
				Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
				clean_tree(c); clean_tree(d);
				r = join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				c = join(join(a, clone(v), fnc[PROD].ex), join(clone(u->tleft), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
				d = join(join(b, clone(u), fnc[PROD].ex), join(clone(v->tleft), NULL, fnc[SINH_F].ex), fnc[PROD].ex);
				return join(join(c, d, fnc[ADD].ex), simplify(r), fnc[DIVID].ex);
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == COS_F && vtok == SINH_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(u->tleft, x, c), * b = coefficient_gpe(v->tleft, x, c);
				Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
				clean_tree(c); clean_tree(d);
				r = join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				c = join(join(a, clone(v), fnc[PROD].ex), join(clone(u->tleft), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
				d = join(join(b, clone(u), fnc[PROD].ex), join(clone(v->tleft), NULL, fnc[COSH_F].ex), fnc[PROD].ex);
				return join(join(c, d, fnc[ADD].ex), simplify(r), fnc[DIVID].ex);
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == COSH_F && vtok == SIN_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, c), * b = coefficient_gpe(u->tleft, x, c);
				Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
				clean_tree(c); clean_tree(d);
				r = join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				c = join(join(b, clone(v), fnc[PROD].ex), join(clone(u->tleft), NULL, fnc[SINH_F].ex), fnc[PROD].ex);
				d = join(join(a, clone(u), fnc[PROD].ex), join(clone(v->tleft), NULL, fnc[COS_F].ex), fnc[PROD].ex);
				return join(join(c, d, fnc[SUB].ex), simplify(r), fnc[DIVID].ex);
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == SIN_F && vtok == SINH_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(u->tleft, x, c), * b = coefficient_gpe(v->tleft, x, c);
				Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
				clean_tree(c); clean_tree(d);
				r = join(r, join(clone(b), new_tree("2"), fnc[POW].ex), fnc[ADD].ex);
				c = join(join(a, clone(v), fnc[PROD].ex), join(clone(u->tleft), NULL, fnc[COS_F].ex), fnc[PROD].ex);
				d = join(join(b, clone(u), fnc[PROD].ex), join(clone(v->tleft), NULL, fnc[COSH_F].ex), fnc[PROD].ex);
				return join(join(d, c, fnc[SUB].ex), simplify(r), fnc[DIVID].ex);
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == COSH_F && vtok == SINH_F)
		{
			Tree* c = degree_sv(u->tleft, x), * d = degree_sv(v->tleft, x);
			if (!strcmp(c->value, "1") && !strcmp(d->value, "1"))
			{
				Tree* a = coefficient_gpe(v->tleft, x, c), * b = coefficient_gpe(u->tleft, x, c);
				clean_tree(c); clean_tree(d);
				if (tree_compare(u->tleft, v->tleft))
				{
					clean_tree(b);
					b = join(new_tree("4"), a, fnc[PROD].ex);
					c = join(new_tree("2"), clone(u->tleft), fnc[PROD].ex);
					d = join(clone(c), NULL, fnc[SINH_F].ex);
					return join(join(d, c, fnc[SUB].ex), b, fnc[DIVID].ex);
				}
				else
				{
					Tree* r = join(clone(a), new_tree("2"), fnc[POW].ex);
					r = join(join(clone(b), new_tree("2"), fnc[POW].ex), r, fnc[SUB].ex);
					c = join(a, join(clone(u->tleft), NULL, fnc[COSH_F].ex), fnc[PROD].ex);
					c = join(c, join(clone(v->tleft), NULL, fnc[SINH_F].ex), fnc[PROD].ex);
					d = join(b, clone(f), fnc[PROD].ex);
					return join(join(d, c, fnc[SUB].ex), simplify(r), fnc[DIVID].ex);
				}
			}
			clean_tree(c); clean_tree(d);
		}
		else if (utok == COS_F && vtok == COS_F)
		{
			if (ismonomial(u->tleft, x) && ismonomial(v->tleft, x))
			{
				Tree* deg_u = degree_sv(u->tleft, x), * deg_v = degree_sv(v->tleft, x);
				if (!strcmp(deg_u->value, "1") && !strcmp(deg_v->value, "1"))
				{
					clean_tree(deg_v);
					Tree* p = coefficient_gpe(u->tleft, x, deg_u), * q = coefficient_gpe(v->tleft, x, deg_u);
					Tree* m = simplify(join(clone(p), clone(q), fnc[SUB].ex));
					Tree* n = simplify(join(p, q, fnc[ADD].ex));
					Tree* m_ = simplify(join(new_tree("2"), clone(m), fnc[PROD].ex));
					Tree* n_ = simplify(join(new_tree("2"), clone(n), fnc[PROD].ex));
					Tree* r = join(join(join(m, new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), m_, fnc[DIVID].ex);
					Tree* s = join(join(join(n, new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), n_, fnc[DIVID].ex);
					clean_tree(deg_u);
					return join(r, s, fnc[ADD].ex);
				}
				clean_tree(deg_u); clean_tree(deg_v);
			}
		}
		else if (utok == SIN_F && vtok == SIN_F)
		{
			if (ismonomial(u->tleft, x) && ismonomial(v->tleft, x))
			{
				Tree* deg_u = degree_sv(u->tleft, x), * deg_v = degree_sv(v->tleft, x);
				if (!strcmp(deg_u->value, "1") && !strcmp(deg_v->value, "1"))
				{
					clean_tree(deg_v);
					Tree* p = coefficient_gpe(u->tleft, x, deg_u), * q = coefficient_gpe(v->tleft, x, deg_u);
					Tree* m = simplify(join(clone(p), clone(q), fnc[SUB].ex));
					Tree* n = simplify(join(p, q, fnc[ADD].ex));
					Tree* m_ = simplify(join(new_tree("2"), clone(m), fnc[PROD].ex));
					Tree* n_ = simplify(join(new_tree("2"), clone(n), fnc[PROD].ex));
					Tree* r = join(join(join(m, new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), m_, fnc[DIVID].ex);
					Tree* s = join(join(join(n, new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), n_, fnc[DIVID].ex);
					clean_tree(deg_u);
					return join(r, s, fnc[SUB].ex);
				}
				clean_tree(deg_u); clean_tree(deg_v);
			}
		}
	}
	else if (tk == DIVID)
	{
		Tree* u = f->tleft;
		Tree* v = f->tright;
		token utok = u->tok_type, vtok = v->tok_type;
		if (!found_element(v, x))
		{
			Tree* t = integral_table(u, x);
			if (t == NULL)
				return NULL;
			return join(join(new_tree("1"), clone(v), fnc[DIVID].ex), t, fnc[PROD].ex);
		}
		Tree* dv = simplify(diff(v, x));
		Tree* s = simplify(join(clone(u), dv, fnc[DIVID].ex));
		if (!found_element(s, x))
			return join(s, join(join(clone(v), NULL, fnc[ABS_F].ex), NULL, fnc[LN_F].ex), fnc[PROD].ex);
		clean_tree(s);
		if (utok == LN_F && ismonomial(u->tleft, x) && ismonomial(v, x))
		{
			Tree* du = degree_sv(u->tleft, x), * dv = degree_sv(v, x);
			if (!strcmp(du->value, "1") && !strcmp(dv->value, "1"))
			{
				clean_tree(du); clean_tree(dv);
				return join(join(clone(u), new_tree("2"), fnc[POW].ex), new_tree("2"), fnc[DIVID].ex);
			}
			Tree* n = simplify(join(clone(dv), new_tree("1"), fnc[SUB].ex));
			Tree* m = simplify(join(new_tree("1"), dv, fnc[SUB].ex));
			Tree* p = join(new_tree(x), clone(n), fnc[POW].ex);
			Tree* s = join(new_tree(x), m, fnc[POW].ex);
			Tree* r = join(join(clone(u), NULL, fnc[NEGATIF].ex), join(clone(n), p, fnc[PROD].ex), fnc[DIVID].ex);
			Tree* q = join(join(du, s, fnc[PROD].ex), simplify(join(n, new_tree("2"), fnc[POW].ex)), fnc[DIVID].ex);
			return join(r, q, fnc[SUB].ex);
		}
		if (vtok == POW)
		{
			if (v->tleft->tok_type == COS_F && ismonomial(v->tleft->tleft, x))
			{
				Tree* deg = degree_sv(v->tleft->tleft, x);
				if (!strcmp(deg->value, "1") && !found_element(u, x))
				{
					Tree* a = coefficient_gpe(v->tleft->tleft, x, deg);
					if (!strcmp(v->tright->value, "2"))
					{
						clean_tree(deg);
						return join(simplify(join(clone(u), a, fnc[DIVID].ex)), join(clone(v->tleft->tleft), NULL, fnc[TAN_F].ex), fnc[PROD].ex);
					}
					Tree* m = simplify(join(clone(v->tright), new_tree("1"), fnc[SUB].ex));
					Tree* n = simplify(join(clone(v->tright), new_tree("2"), fnc[SUB].ex));
					Tree* r = join(clone(v->tleft->tleft), NULL, fnc[SIN_F].ex);
					Tree* s = join(simplify(join(a, clone(m), fnc[PROD].ex)), join(clone(v->tleft), clone(m), fnc[POW].ex), fnc[PROD].ex);
					Tree* nf = NULL;
					if (!strcmp(n->value, "0"))
						nf = new_tree("1");
					else if (!strcmp(n->value, "1"))
						nf = join(new_tree("1"), clone(v->tleft), fnc[DIVID].ex);
					else
						nf = join(new_tree("1"), join(clone(v->tleft), clone(n), fnc[POW].ex), fnc[DIVID].ex);
					Tree* q = integral_table(nf, x);
					a = simplify(join(m, n, fnc[DIVID].ex));
					clean_tree(deg); clean_tree(nf);
					Tree* ret = join(join(r, s, fnc[DIVID].ex), join(a, q, fnc[PROD].ex), fnc[ADD].ex);
					if (!strcmp(u->value, "1"))
						return ret;
					return join(clone(u), ret, fnc[PROD].ex);
				}
				clean_tree(deg);
			}
			if (v->tleft->tok_type == SIN_F && ismonomial(v->tleft->tleft, x))
			{
				Tree* deg = degree_sv(v->tleft->tleft, x);
				if (!strcmp(deg->value, "1") && !found_element(u, x))
				{
					Tree* a = coefficient_gpe(v->tleft->tleft, x, deg);
					if (!strcmp(v->tright->value, "2"))
					{
						clean_tree(deg);
						return join(join(clone(u), join(a, join(clone(v->tleft->tleft), NULL, fnc[TAN_F].ex), fnc[PROD].ex), fnc[DIVID].ex), NULL, fnc[NEGATIF].ex);
					}
					Tree* m = simplify(join(clone(v->tright), new_tree("1"), fnc[SUB].ex));
					Tree* n = simplify(join(clone(v->tright), new_tree("2"), fnc[SUB].ex));
					Tree* r = join(clone(v->tleft->tleft), NULL, fnc[COS_F].ex);
					Tree* s = join(simplify(join(a, clone(m), fnc[PROD].ex)), join(clone(v->tleft), clone(m), fnc[POW].ex), fnc[PROD].ex);
					Tree* nf = NULL;
					if (!strcmp(n->value, "0"))
						nf = new_tree("1");
					else if (!strcmp(n->value, "1"))
						nf = join(new_tree("1"), clone(v->tleft), fnc[DIVID].ex);
					else
						nf = join(new_tree("1"), join(clone(v->tleft), clone(n), fnc[POW].ex), fnc[DIVID].ex);
					Tree* q = integral_table(nf, x);
					a = simplify(join(m, n, fnc[DIVID].ex));
					clean_tree(deg); clean_tree(nf);
					Tree* ret = join(join(join(r, NULL, fnc[NEGATIF].ex), s, fnc[DIVID].ex), join(a, q, fnc[PROD].ex), fnc[ADD].ex);
					if (!strcmp(u->value, "1"))
						return ret;
					return join(clone(u), ret, fnc[PROD].ex);
				}
				clean_tree(deg);
			}
			Tree* b = NULL;
			if (!strcmp(v->tright->value, "2"))
				b = clone(v->tleft);
			else
			{
				Tree* c = simplify(join(clone(v->tright), new_tree("1"), fnc[SUB].ex));
				b = join(clone(v->tleft), c, fnc[POW].ex);
			}
			Tree* db = simplify(diff(b, x));
			Tree* s = simplify(join(clone(u), db, fnc[DIVID].ex));
			if (isconstant(s))
				return join(s, join(join(new_tree("1"), b, fnc[DIVID].ex), NULL, fnc[NEGATIF].ex), fnc[PROD].ex);
			clean_tree(s); clean_tree(b);
		}
		else if (vtok == SQRT_F || (vtok == POW && isdemi(v->tright)))
		{
			Tree* b = v->tleft;
			Tree* db = simplify(diff(b, x));
			Tree* s = simplify(join(clone(u), db, fnc[DIVID].ex));
			if (!found_element(s, x))
				return join(simplify(join(s, new_tree("2"), fnc[PROD].ex)), clone(v), fnc[PROD].ex);
			clean_tree(s);
		}
		else if (vtok == COS_F && ismonomial(v->tleft, x))
		{
			Tree* deg = degree_sv(v->tleft, x);
			if (!strcmp(deg->value, "1") && !found_element(u, x))
			{
				Tree* a = coefficient_gpe(v->tleft, x, deg);
				Tree* r = join(join(join(new_tree("2"), clone(v->tleft), fnc[PROD].ex), new_tree(fnc[PI].ex), fnc[ADD].ex), new_tree("4"), fnc[DIVID].ex);
				clean_tree(deg);
				return join(simplify(join(clone(u), a, fnc[DIVID].ex)), join(join(r, NULL, fnc[TAN_F].ex), NULL, fnc[LN_F].ex), fnc[PROD].ex);
			}
			clean_tree(deg);
		}
		else if (vtok == SIN_F && ismonomial(v->tleft, x))
		{
			Tree* deg = degree_sv(v->tleft, x);
			if (!strcmp(deg->value, "1") && !found_element(u, x))
			{
				Tree* a = coefficient_gpe(v->tleft, x, deg);
				Tree* r = join(clone(v->tleft), new_tree("2"), fnc[DIVID].ex);
				clean_tree(deg);
				return join(simplify(join(clone(u), a, fnc[DIVID].ex)), join(join(r, NULL, fnc[TAN_F].ex), NULL, fnc[LN_F].ex), fnc[PROD].ex);
			}
			clean_tree(deg);
		}
		else if ((vtok == ADD || vtok == SUB) && ispoly(v, x))
		{
			Tree* deg = degree_sv(v, x);
			if (!strcmp(deg->value, "1"))
			{
				if (!strcmp(u->value, x))
				{
					Tree* a = coefficient_gpe(v, x, deg);
					deg = simplify(join(deg, new_tree("1"), fnc[SUB].ex));
					Tree* b = coefficient_gpe(v, x, deg);
					clean_tree(deg);
					deg = join(join(b, join(clone(a), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex), join(clone(v), NULL, fnc[LN_F].ex), fnc[PROD].ex);
					return join(join(clone(u), a, fnc[DIVID].ex), deg, fnc[SUB].ex);
				}
				clean_tree(deg);
			}
			else if (!strcmp(deg->value, "2"))
			{
				map Li = NULL;
				for (int i = 0; i < 3; i++)
				{
					Tree* k = coefficient_gpe(v, x, deg);
					Li = push_back_map(Li, k);
					clean_tree(k);
					deg = simplify(join(deg, new_tree("1"), fnc[SUB].ex));
				}
				clean_tree(deg);
				Tree* a = Li->begin->tr, * b = Li->begin->next->tr, * c = Li->end->tr;
				if (!strcmp(b->value, "0"))
				{
					if (!found_element(u, x))
					{
						if (!is_negation(a) && !is_negation(c))
						{
							Tree* p = simplify(join(clone(u), join(join(clone(a), clone(c), fnc[PROD].ex), NULL, fnc[SQRT_F].ex), fnc[DIVID].ex));
							s = simplify(join(join(clone(a), clone(c), fnc[DIVID].ex), NULL, fnc[SQRT_F].ex));
							Li = clear_map(Li);
							return join(p, join(join(new_tree(x), s, fnc[PROD].ex), NULL, fnc[ATAN_F].ex), fnc[PROD].ex);
						}
						else if (is_negation(a) && is_negation(c))
						{
							Tree* a_ = simplify(join(clone(a), NULL, fnc[ABS_F].ex));
							Tree* c_ = simplify(join(clone(c), NULL, fnc[ABS_F].ex));
							Tree* p = simplify(join(clone(u), join(join(clone(a_), clone(c_), fnc[PROD].ex), NULL, fnc[SQRT_F].ex), fnc[DIVID].ex));
							s = simplify(join(join(a_, c_, fnc[DIVID].ex), NULL, fnc[SQRT_F].ex));
							Li = clear_map(Li);
							return join(join(p, NULL, fnc[NEGATIF].ex), join(join(new_tree(x), s, fnc[PROD].ex), NULL, fnc[ATAN_F].ex), fnc[PROD].ex);
						}
						else if (is_negation(a) || is_negation(c))
						{
							Tree* ra = simplify(join(join(clone(a), NULL, fnc[ABS_F].ex), NULL, fnc[SQRT_F].ex));
							Tree* rc = simplify(join(join(clone(c), NULL, fnc[ABS_F].ex), NULL, fnc[SQRT_F].ex));
							Tree* num = NULL, * dnm = NULL;
							if (is_negation(a))
							{
								num = join(clone(rc), join(ra, new_tree(x), fnc[PROD].ex), fnc[ADD].ex);
								dnm = join(rc, join(clone(ra), new_tree(x), fnc[PROD].ex), fnc[SUB].ex);
							}
							else
							{
								dnm = join(rc, join(clone(ra), new_tree(x), fnc[PROD].ex), fnc[ADD].ex);
								num = join(join(ra, new_tree(x), fnc[PROD].ex), clone(rc), fnc[SUB].ex);
							}
							s = join(join(join(clone(a), clone(c), fnc[PROD].ex), NULL, fnc[ABS_F].ex), NULL, fnc[SQRT_F].ex);
							s = simplify(join(clone(u), join(new_tree("2"), s, fnc[PROD].ex), fnc[DIVID].ex));
							Li = clear_map(Li);
							return join(s, join(join(num, dnm, fnc[DIVID].ex), NULL, fnc[LN_F].ex), fnc[PROD].ex);
						}
					}
					else if (utok == POW && !strcmp(u->tleft->value, x) && u->tright->gtype == ENT)
					{
						Tree* m = exponent(u);
						Tree* n = simplify(join(clone(m), new_tree("2"), fnc[SUB].ex));
						Tree* p = NULL;
						s = simplify(join(m, new_tree("1"), fnc[SUB].ex));
						Tree* r = simplify(join(new_tree(x), clone(s), fnc[POW].ex));
						Tree* t = simplify(join(clone(c), clone(a), fnc[DIVID].ex));
						Tree* q = simplify(join(clone(a), s, fnc[PROD].ex));
						if (!strcmp(n->value, "0"))
							p = join(new_tree("1"), clone(v), fnc[DIVID].ex);
						else if (!strcmp(n->value, "1"))
							p = join(new_tree(x), clone(v), fnc[DIVID].ex);
						else
							p = join(join(new_tree(x), clone(n), fnc[POW].ex), clone(v), fnc[DIVID].ex);
						Tree* w = integral_table(p, x);
						Li = clear_map(Li);
						clean_tree(p); clean_tree(n);
						return join(join(r, q, fnc[DIVID].ex), join(t, w, fnc[PROD].ex), fnc[SUB].ex);
					}
				}
				Li = clear_map(Li);
			}
			else
				clean_tree(deg);
		}
	}
	else if (tk == POW)
	{
		Tree* u = f->tleft;
		Tree* v = f->tright;
		token utok = u->tok_type;
		if (ispoly(u, x) && !found_element(v, x))
		{
			Tree* w = simplify(join(clone(v), new_tree("1"), fnc[ADD].ex));
			if (!strcmp(w->value, "0"))
			{
				Tree* c = join(new_tree("1"), clone(u), fnc[DIVID].ex);
				Tree* r = integral_table(c, x);
				clean_tree(c);clean_tree(w);
				return r;
			}
			if (ismonomial(u, x))
				return join(join(clone(u), clone(w), fnc[POW].ex), w, fnc[DIVID].ex);
		}
		else if (v->gtype == ENT)
		{
			if (utok == SIN_F)
			{
				Tree* d = degree_sv(u->tleft, x);
				if (!strcmp(d->value, "1"))
				{
					Tree* a = coefficient_gpe(u->tleft, x, d);
					Tree* n1 = join(clone(v), new_tree("1"), fnc[SUB].ex);
					Tree* n2 = join(clone(v), new_tree("2"), fnc[SUB].ex);
					Tree* z = join(new_tree("1"), join(clone(v), a, fnc[PROD].ex), fnc[DIVID].ex);
					Tree* s = join(clone(u->tleft), NULL, fnc[SIN_F].ex);
					Tree* r = join(clone(u->tleft), NULL, fnc[COS_F].ex);
					Tree* nf = NULL, * o = NULL;
					n1 = simplify(n1);
					n2 = simplify(n2);
					if (!strcmp(n2->value, "0"))
						nf = new_tree("1");
					else if (!strcmp(n2->value, "1"))
						nf = clone(s);
					else
						nf = join(clone(s), clone(n2), fnc[POW].ex);
					o = join(clone(n1), clone(v), fnc[DIVID].ex);
					z = join(join(join(join(s, n1, fnc[POW].ex), NULL, fnc[NEGATIF].ex), r, fnc[PROD].ex), simplify(z), fnc[PROD].ex);
					clean_tree(d); clean_tree(n2);
					d = integral_table(nf, x);
					clean_tree(nf);
					return join(z, join(o, d, fnc[PROD].ex), fnc[ADD].ex);
				}
				clean_tree(d);
			}
			else if (utok == COS_F)
			{
				Tree* d = degree_sv(u->tleft, x);
				if (!strcmp(d->value, "1"))
				{
					Tree* a = coefficient_gpe(u->tleft, x, d);
					Tree* n1 = join(clone(v), new_tree("1"), fnc[SUB].ex);
					Tree* n2 = join(clone(v), new_tree("2"), fnc[SUB].ex);
					Tree* z = join(new_tree("1"), join(clone(v), a, fnc[PROD].ex), fnc[DIVID].ex);
					Tree* s = join(clone(u->tleft), NULL, fnc[COS_F].ex);
					Tree* r = join(clone(u->tleft), NULL, fnc[SIN_F].ex);
					Tree* nf = NULL, * o = NULL;
					n1 = simplify(n1);
					n2 = simplify(n2);
					if (!strcmp(n2->value, "0"))
						nf = new_tree("1");
					else if (!strcmp(n2->value, "1"))
						nf = clone(s);
					else
						nf = join(clone(s), clone(n2), fnc[POW].ex);
					o = join(clone(n1), clone(v), fnc[DIVID].ex);
					z = join(join(join(s, n1, fnc[POW].ex), r, fnc[PROD].ex), simplify(z), fnc[PROD].ex);
					clean_tree(d); clean_tree(n2);
					d = integral_table(nf, x);
					clean_tree(nf);
					return join(z, join(o, d, fnc[PROD].ex), fnc[ADD].ex);
				}
				clean_tree(d);
			}
			else if (utok == LN_F)
			{
				Tree* c = simplify(join(clone(v), new_tree("1"), fnc[SUB].ex));
				Tree* r = join(new_tree(x), clone(f), fnc[PROD].ex);
				Tree* s = NULL;
				if (!strcmp(c->value, "1"))
				{
					clean_tree(c);
					s = integral_table(u, x);
				}
				else
				{
					Tree* q = join(clone(u), c, fnc[POW].ex);
					s = integral_table(q, x);
					clean_tree(q);
				}
				return join(r, join(clone(v), s, fnc[PROD].ex), fnc[SUB].ex);
			}
		}
	}
	return NULL;
}

static Tree* linear_priorities(Tree* f, const char* x)
{
	if (f->tok_type == PROD)
	{
		Tree* u = f->tleft;
		Tree* v = f->tright;
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
			if (s == NULL)
				return NULL;
			return join(clone(v), s, fnc[PROD].ex);
		}
	}
	else if (f->tok_type == ADD || f->tok_type == SUB)
	{
		Tree* s = integral(f->tleft, x);
		Tree* t = integral(f->tright, x);
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
	Tree* F = NULL;
	Tree* v = new_tree("XX");
	mapCell* tmp = P->begin;
	while (tmp != NULL && !F)
	{
		Tree* g = tmp->tr;
		if (!found_element(g, x))
		{
			Tree* d = diff(g, x);
			Tree* u = join(clone(f), d, fnc[DIVID].ex);
			Tree* s = substitute(u, g, v);
			s = simplify(s);
			if (!found_element(s, x) && strcmp(s->value, fnc[UNDEF].ex))
				F = remplace_tree(integral(s, v->value), v->value, g);
			clean_tree(u); clean_tree(s);
		}
		tmp = tmp->next;
	}
	P = clear_map(P);
	clean_tree(v);
	return F;
}

static Tree* integral(Tree* f, const char* x)
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
	return F;
}

/* analyse */

Tree* analyse(Tree* tr)
{
	token tk = tr->tok_type;
	if (tk == DERIV_F)
	{
		Tree* t = tr->tleft;
		if (t->tok_type != SEPARATEUR)
        {
            clean_tree(tr);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		if (t->tleft->tok_type == SEPARATEUR)
		{
			Tree* r = clone(t->tleft->tleft);
			Tree* a = clone(t->tleft->tright);
			Tree* b = clone(t->tright);
			if (r->tok_type == SEPARATEUR || (b->gtype != ENT && b->gtype != VAR) || a->gtype != VAR)
			{
                clean_tree(tr); clean_tree(r); clean_tree(a); clean_tree(b);
			    Error = push_back_dlist(Error, "Erreur arguments.");
                return NULL;
            }
			Tree* res = NULL;
			if (b->gtype == ENT)
				res = simplify(diff_n(r, a->value, (int)tonumber(b->value)));
			else if (b->gtype == VAR && !strcmp(a->value, b->value))
                res = simplify(diff(r, a->value));
            else
				res = simplify(diff_partial(r, a->value, b->value));
			clean_tree(r); clean_tree(a); clean_tree(b);
			return pow_transform(res);
		}
		if (t->tright->gtype == VAR)
		{
            Tree* r = clone(t->tleft), * x = t->tright;
            clean_tree(tr);
			Tree* res = diff(r, x->value);
            clean_tree(r); clean_tree(x);
			return pow_transform(simplify(res));
		}
		return tr;
	}
	else if (tk == TAYLOR_F)
	{
		Tree* t = tr->tleft;
		map L = NULL;
		for (int i = 0; i < 3; i++)
		{
			if (t->tok_type != SEPARATEUR)
			{
				if (L != NULL)
					L = clear_map(L);
                clean_tree(tr);
				return NULL;
			}
			else
			{
				L = push_front_map(L, t->tright);
				t = t->tleft;
			}
		}
		Tree* a = clone(L->begin->tr);
		Tree* b = clone(L->begin->next->tr);
		Tree* c = clone(L->end->tr);
        t = clone(t);
        clean_tree(tr);
		L = clear_map(L);
		Tree* res = taylor(t, a, b, c);
		clean_tree(t); clean_tree(a); clean_tree(b); clean_tree(c);
		if (res == NULL)
			return NULL;
        return pow_transform(res);
	}
	else if (tk == TANG_F)
	{
		Tree* t = tr->tleft;
		if (t->tok_type != SEPARATEUR)
        {
            clean_tree(tr);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		Tree* b = clone(t->tright);
		t = t->tleft;
		if (t->tok_type != SEPARATEUR || b->gtype == VAR)
        {
            clean_tree(b); clean_tree(tr);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		Tree* a = clone(t->tright);
		t = clone(t->tleft);
        clean_tree(tr);
		Tree* w = tangline(t, a->value, b);
		clean_tree(t); clean_tree(a); clean_tree(b);
		return pow_transform(w);
	}
	else if (tk == INTEGRAL_F)
	{
		Tree* t = tr->tleft;
		if (t->tok_type != SEPARATEUR)
        {
            clean_tree(tr);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		while (t->tleft->tok_type == SEPARATEUR)
			t = t->tleft;
		t->tleft = pow_transform(Contract_pow(simplify(t->tleft)));
        Tree* f = clone(t->tleft), * x = clone(t->tright);
        clean_tree(tr);
		Tree* res = integral(f, x->value);
        clean_tree(f); clean_tree(x);
		if (res == NULL)
        {
			Error = push_back_dlist(Error, "Non géré.");
            return NULL;
        }
		return pow_transform(simplify(res));
	}
	else if (tk == DESOLVE_F)
	{
		Tree* t = tr->tleft;
		if (t->tok_type != SEPARATEUR)
        {
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		Tree* y = clone(t->tright);
		t = t->tleft;
		if (t->tok_type != SEPARATEUR)
        {
            clean_tree(y);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		Tree* x = clone(t->tright);
		t = t->tleft;
        DList vrs = NULL;
		vrs = getvars(t, vrs);
        DListCell* k = vrs->begin;
		int i = 1, li[10], j = 0;
		while (k != NULL)
		{
			if (!strstr(k->value, y->value))
			{
				li[j] = i;
				j++;
			}
			k = k->next;
			i++;
		}
		for (i = 0; i < j; i++)
		{
			vrs = dlist_remove_id(vrs, li[i]);
		}
		vrs = dlist_sortD(vrs);
        if (vrs == NULL || vrs->length > 3 || vrs->length < 2 || strlen(vrs->begin->value) - strlen(y->value) > 2)
        {
            clean_tree(x); clean_tree(y);
            if (vrs != NULL)
            {
                vrs = clear_dlist(vrs);
            }
			Error = push_back_dlist(Error, "Erreur arguments. Verifiez la saisie.");
            return NULL;
        }
		if (vrs != NULL && vrs->length == 2 && !strcmp(vrs->end->value, y->value) && strlen(vrs->begin->value) - strlen(y->value) == 1)
		{
			Tree* cond1 = NULL;
			if (t->tok_type == LOGIC_AND)
			{
                if (t->tleft->tok_type != EGAL)
                {
                    clean_tree(x); clean_tree(y);
        			Error = push_back_dlist(Error, "Erreur arguments conditions.");
                    return NULL;
                }
				cond1 = clone(t->tright);
				t = t->tleft;
			}
            Tree* f = clone(t->tright);
            t = t->tleft;
			Tree* un = new_tree("1");
			Tree* b = coefficient_gpe(t, vrs->begin->value, un);
			Tree* a = coefficient_gpe(t, y->value, un);
            vrs = clear_dlist(vrs);
			clean_tree(un); clean_tree(tr);
			Tree* p = solve_ode(a, b, f, x->value, y->value, cond1);
			return pow_transform(p);
		}
		Tree* cond1 = NULL, * cond2 = NULL;
		if (t->tok_type == LOGIC_AND)
		{
            if (t->tleft->tleft->tok_type != EGAL || t->tleft->tok_type != LOGIC_AND)
            {
                clean_tree(x); clean_tree(y);
			Error = push_back_dlist(Error, "Erreur arguments conditions.");
                return NULL;
            }
			cond2 = clone(t->tright);
			t = t->tleft;
			cond1 = clone(t->tright);
			t = t->tleft;
		}
		Tree* f = clone(t->tright);
		t = t->tleft;
		Tree* un = new_tree("1"), * a = coefficient_gpe(t, vrs->begin->value, un), * b = NULL, * c = NULL;
		if (vrs->length == 3)
        {
            b = coefficient_gpe(t, vrs->begin->next->value, un);
            c = coefficient_gpe(t, y->value, un);
        }
        else
        {
            if (!strcmp(vrs->end->value, y->value))
            {
                b = new_tree("0");
                c = coefficient_gpe(t, y->value, un);
            }
            else
            {
                c = new_tree("0");
                b = coefficient_gpe(t, vrs->end->value, un);
            }
        }
        vrs = clear_dlist(vrs);
        clean_tree(un); clean_tree(tr);
		Tree* p = solve_ode_2(a, b, c, f, x->value, y->value, cond1, cond2);
        clean_tree(x); clean_tree(y);
        return pow_transform(p);
	}
	else if (tk == EXPAND_F)
	{
        if (tr->tleft->tok_type == SEPARATEUR)
        {
			Error = push_back_dlist(Error, "Erreur Trop d'arguments.");
            return NULL;
        }
		TRIG_EXPAND = true;
		LN_EXP_EXPAND = true;
		ALG_EXPAND = true;
		Tree* s = algebraic_expand(tr->tleft);
		clean_noeud(tr);
		return simplify(s);
	}
    else if (tk == REMAINDER_F || tk == INT_F || tk == GCD_F || tk == POLYSIMP_F)
	{
		Tree* t = tr->tleft;
		if (t->tok_type != SEPARATEUR)
        {
            clean_tree(tr);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		Tree* b = clone(t->tright);
		t = t->tleft;
		if (t->tok_type != SEPARATEUR)
        {
            clean_tree(b); clean_tree(tr);
			Error = push_back_dlist(Error, "Erreur arguments.");
            return NULL;
        }
		Tree* a = clone(t->tright), * r = NULL;
		t = clone(t->tleft);
        clean_tree(tr);
		if (tk == REMAINDER_F)
			r = poly_remainder(polynomial_division(t, a, b->value));
		else if (tk == INT_F)
			r = poly_quotient(polynomial_division(t, a, b->value));
		else if (tk == POLYSIMP_F)
			r = poly_simp(t, a, b->value);
        else
			r = poly_gcd(t, a, b->value);
        clean_tree(t); clean_tree(a); clean_tree(b);
		return pow_transform(r);
	}
	else
    {
        /*if (tk == SIN_F || tk == COS_F)
            TRIGO_EXACT_SEARCH = true;*/
        return pow_transform(Contract_pow(simplify(tr)));
    }
}
