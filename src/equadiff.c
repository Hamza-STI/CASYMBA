#include "includes.h"

static Tree* sub_ode(Tree* tr, const char** vrs, map Li)
{
	int i = 0;
	for (Cell* tmp = Li->begin; tmp != NULL; tmp = tmp->next)
		tr = remplace_var(tr, vrs[i++], tmp->data);
	return tr;
}

static Tree* trig_separe(Tree* f, const char* x, Tree** part)
{
	map M = map_create_prod(f);
	Tree* part_trig = NULL;
	for (Cell* tmp = M->begin; tmp != NULL; tmp = tmp->next)
	{
		if ((((Tree*)tmp->data)->tok_type == SIN_F || ((Tree*)tmp->data)->tok_type == COS_F) && found_element(((Tree*)tmp->data), x))
			part_trig = clone(tmp->data);
		else
			*part = (*part == NULL) ? clone(tmp->data) : join(*part, clone(tmp->data), fnc[PROD].ex);
	}
	if (*part == NULL)
		*part = new_tree("1");
	M = clear_map(M);
	return part_trig;
}

static map homogenious_2(Tree* a, Tree* b, Tree* c, const char* x, map* S)
{
	if (!strcmp(a->value, "1") && !strcmp(b->value, "0"))
	{
		Tree* d = simplify(join(clone(c), NULL, fnc[SQRT_F].ex));
		Tree* t = join(clone(d), new_tree(x), fnc[PROD].ex);
		Tree* cs = join(clone(t), NULL, fnc[COS_F].ex), * sn = join(t, NULL, fnc[SIN_F].ex);
		*S = push_back(*S, d);
		return push_back(push_back(NULL, cs), sn);
	}
	Tree* D = (join(clone((b->tok_type == NEGATIF) ? b->tleft : b), new_tree("2"), fnc[POW].ex));
	Tree* e = (join(join(new_tree("4"), clone(a), fnc[PROD].ex), clone(c), fnc[PROD].ex));
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
		return push_back(push_back(NULL, y1), y2);
	}
	else if (d == 0)
	{
		clean_tree(D);
		Tree* com = simplify(join(join(clone(b), join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex), NULL, fnc[NEGATIF].ex));
		*S = push_back_map(*S, com);
		com = join(join(com, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* y = join(clone(com), new_tree(x), fnc[PROD].ex);
		return push_back(push_back(NULL, com), y);
	}
	else if (d < 0)
	{
		e = (b->tok_type == NEGATIF) ? clone(b->tleft) : join(clone(b), NULL, fnc[NEGATIF].ex);
		Tree* com = simplify(join(e, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex));
		*S = push_back_map(*S, com);
		com = join(join(com, new_tree(x), fnc[PROD].ex), NULL, fnc[EXP_F].ex);
		Tree* r = join(join(D, NULL, fnc[NEGATIF].ex), NULL, fnc[SQRT_F].ex);
		r = simplify(join(r, join(new_tree("2"), clone(a), fnc[PROD].ex), fnc[DIVID].ex));
		*S = push_back_map(*S, r);
		Tree* y1 = join(clone(com), join(join(clone(r), new_tree(x), fnc[PROD].ex), NULL, fnc[SIN_F].ex), fnc[PROD].ex);
		Tree* y2 = join(com, join(join(r, new_tree(x), fnc[PROD].ex), NULL, fnc[COS_F].ex), fnc[PROD].ex);
		return push_back(push_back(NULL, y1), y2);
	}
	return NULL;
}

static Tree* system_rmp(Tree* tr, List v, map L)
{
	for (Cell* tmp = v->begin, * tmp_L = L->begin; tmp != NULL; tmp = tmp->next, tmp_L = tmp_L->next)
		tr = remplace_var(tr, (char*)tmp->data, tmp_L->data);
	return tr;
}

static map solve_system(map* L, map* R)
{
	Cell* tmp_L = (*L)->begin, * tmp_R = (*R)->begin;
	List vrs = NULL, v_ps = NULL;
	map rt = NULL;
	while (tmp_L != NULL)
	{
		Tree* t = clone(tmp_L->data);
		if (v_ps != NULL)
			t = system_rmp(t, v_ps, rt);
		vrs = getvars(t, vrs);
		if (vrs != NULL && vrs->length == 1)
		{
			map cf = polycoeffs(t, vrs->end->data);
			Tree* q = simplify(join(join(clone(tmp_R->data), clone(cf->end->data), fnc[SUB].ex), clone(cf->begin->data), fnc[DIVID].ex));
			cf = clear_map(cf);
			v_ps = push_back_dlist(v_ps, vrs->end->data);
			rt = push_back(rt, q);
		}
		else if (vrs == NULL && ((rt != NULL && rt->length < (*R)->length) || rt == NULL))
			rt = push_back_map(rt, t);
		vrs = clear_dlist(vrs);
		clean_tree(t);
		tmp_L = tmp_L->next;
		tmp_R = tmp_R->next;
		if (tmp_L == NULL && (rt == NULL || rt->length < (*R)->length))
		{
			tmp_L = (*L)->begin;
			tmp_R = (*R)->begin;
		}
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
		v = join(v, clone(dg), fnc[POW].ex);
	return join(w, v, fnc[PROD].ex);
}

static Tree* poly_solution_2(Tree* a, Tree* b, Tree* c, Tree* part, const char* x, Tree* dg)
{
	Tree* Pl = NULL;
	int w = (int)tonumber(dg->value);
	List cf = NULL, cpl = NULL, sol = NULL, vr = NULL;
	for (int i = w; i >= 0; i--)
		cpl = push_back(cpl, new_tree("0"));
	for (int i = w; i >= 0; i--)
	{
		char ct[] = { 'M', '0' + i, '\0' };
		vr = push_back_dlist(vr, ct);
		cf = push_front(cf, coefficient_gpe(part, x, i));
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
	for (Cell* tmp = sol->begin, * cel_vr = vr->begin; tmp != NULL; tmp = tmp->next, cel_vr = cel_vr->next)
		Pl = remplace_var(Pl, cel_vr->data, tmp->data);
	vr = clear_dlist(vr);
	sol = clear_map(sol);
	return simplify(Pl);
}

static Tree* exp_solution_2(Tree* a, Tree* b, Tree* c, const char* x, Tree* dg, Tree* part, Tree* part_exp, Tree* r)
{
	Tree* u = NULL, * v = NULL;
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
	return join(poly_solution_2(a, u, v, part, x, dg), part_exp, fnc[PROD].ex);
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
		map Li = push_back(push_back(push_back(push_back(push_back(push_back(NULL, a), b), c), r), c_x1), s_x1);
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
		Li = push_back(push_back(push_back_map(push_back_map(pop_back_map(pop_back_map(Li)), m1), m3), c_x0), s_x0);
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
		clean_tree(a); clean_tree(b);
		return simplify(join(f, c, fnc[DIVID].ex));
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
			Cell* tmp;
			clean_tree(f);
			for (tmp = M->begin; tmp != NULL; tmp = tmp->next)
			{
				if (((Tree*)tmp->data)->tok_type == EXP_F && found_element((Tree*)tmp->data, x))
					part_exp = clone(tmp->data);
				else
					part = (part == NULL) ? clone(tmp->data) : join(part, clone(tmp->data), fnc[PROD].ex);
			}
			if (part == NULL)
				part = new_tree("1");
			M = clear_map(M);
			Tree* r = coefficient_gpe(part_exp->tleft, x, 1), * dg = degree_sv(part, x);
			for (tmp = S->begin; tmp != NULL; tmp = tmp->next)
			{
				if (tree_compare(r, tmp->data))
				{
					dg = simplify(join(dg, new_tree((strcmp(a->value, "0") && S->length == 1) ? "2" : "1"), fnc[ADD].ex));
					break;
				}
			}
			return exp_solution_2(a, b, c, x, dg, part, part_exp, r);
		}
		else if ((sn || cs) && !e)
		{
			Tree* trig = NULL, * part = NULL, * part1 = NULL, * trig1 = NULL;
			if (f->tok_type == PROD && (f->tleft->tok_type == ADD || f->tleft->tok_type == SUB || f->tright->tok_type == ADD || f->tright->tok_type == SUB))
			{
				TRIG_EXPAND = false;
				Tree* F = simplify(expand(f)), * p = f->parent;
				clean_tree(f);
				f = F;
				f->parent = p;
			}
			if (f->tok_type == ADD || f->tok_type == SUB)
			{
				map R = map_create_add(f);
				int k = R->length;
				clean_tree(f);
				trig = trig_separe(R->begin->data, x, &part);
				trig1 = trig_separe(R->end->data, x, &part1);
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
			if (tree_compare(nx, S->end->data))
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
	if (vrs != NULL && vrs->length == 1 && strstr(vrs->begin->data, y))
	{
		int p = strlen(vrs->begin->data) - strlen(y);
		if (p > 1)
		{
			vrs = clear_dlist(vrs);
			return NULL;
		}
		*point = coefficient_gpe(cond, vrs->begin->data, 1);
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
	return push_back(push_back(push_back(NULL, i), j), d);
}

Tree* solve_ode_2(Tree* a, Tree* b, Tree* c, Tree* f, const char* x, const char* y, Tree* cond1, Tree* cond2)
{
	map S = NULL;
	map L = homogenious_2(a, b, c, x, &S);
	Tree* yh = join(join(new_tree("A"), clone(L->begin->data), fnc[PROD].ex), join(new_tree("B"), clone(L->end->data), fnc[PROD].ex), fnc[ADD].ex);
	L = clear_map(L);
	Tree* par_sol = solve_exact_2(a, b, c, f, S, x); //recherche solution particulière
	S = clear_map(S);
	if (par_sol == NULL)
	{
		clean_tree(yh);
		Error = push_back_dlist(Error, err_msg[1]);
		return NULL;
	}
	yh = simplify(join(yh, par_sol, fnc[ADD].ex));
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
		num1 = simplify(join(join(clone(cf2->begin->next->data), clone(cond1->tright), fnc[PROD].ex), join(clone(cf1->begin->next->data), clone(cf2->end->data), fnc[PROD].ex), fnc[SUB].ex));
		num2 = simplify(join(join(clone(cf1->begin->data), clone(cond2->tright), fnc[PROD].ex), join(clone(cf2->begin->data), clone(cf1->end->data), fnc[PROD].ex), fnc[SUB].ex));
		clean_tree(cond1); clean_tree(cond2);
		denom = simplify(join(join(clone(cf2->begin->next->data), clone(cf1->begin->data), fnc[PROD].ex), join(clone(cf1->begin->next->data), clone(cf2->begin->data), fnc[PROD].ex), fnc[SUB].ex));
		v = simplify(join(num1, clone(denom), fnc[DIVID].ex));
		w = simplify(join(num2, denom, fnc[DIVID].ex));
		yh = remplace_var(remplace_var(yh, "A", v), "B", w);
		clean_tree(v); clean_tree(w);
		cf1 = clear_map(cf1); cf2 = clear_map(cf2);
		yh = simplify(yh);
	}
	return join(new_tree(y), yh, fnc[EGAL].ex);
}

Tree* solve_ode(Tree* M, Tree* N, Tree* f, const char* x, const char* y, Tree* cond)
{
	Tree* r = simplify(join(join(clone(M), clone(N), fnc[DIVID].ex), NULL, fnc[NEGATIF].ex));
	Tree* R = simplify(integral(r, x));
	Tree* s = join(new_tree("K"), join(R, NULL, fnc[EXP_F].ex), fnc[PROD].ex);
	map S = push_back(NULL, r);
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
		clean_tree(dr); clean_tree(p);
		Tree* k = simplify(join(join(clone(cond->tright), clone(cf->end->data), fnc[SUB].ex), clone(cf->begin->data), fnc[DIVID].ex));
		cf = clear_map(cf);
		s = simplify(remplace_var(s, "K", k));
		clean_tree(k); clean_tree(cond);
	}
	return join(new_tree(y), s, fnc[EGAL].ex);
}